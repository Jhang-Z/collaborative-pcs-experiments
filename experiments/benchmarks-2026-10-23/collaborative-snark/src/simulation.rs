//! Sequential real execution with public per-exchange timings for virtual LAN replay.
use crate::{prepare::Shape, worker::Worker, preprocessing::PublicPreprocessing, wire};
use anyhow::{Result, ensure, Context};
use serde::Serialize;
use serde_json::Value;
use std::{fs, io::{Read, Write}, path::{Path, PathBuf}, time::Instant, sync::Arc,
    fs::File, os::fd::{FromRawFd,AsRawFd}, os::unix::process::ExitStatusExt};

/// Linux process samples, not allocator payload or aggregate cluster peak memory.
pub(crate) fn process_memory(pid:u32)->Value {
    let Ok(status)=fs::read_to_string(format!("/proc/{pid}/status")) else { return Value::Null; };
    let mut memory=serde_json::json!({"pid":pid,"scope":"one process /proc/status sample; kB"});
    for (name,key) in [("VmRSS:","rss_kb"),("VmHWM:","high_water_kb")] {
        if let Some(value)=status.lines().find_map(|line|line.strip_prefix(name)).and_then(|s|s.split_whitespace().next()).and_then(|s|s.parse::<u64>().ok()) {memory[key]=value.into();}
    }
    memory["cpu_allowed_list"]=status.lines().find_map(|line|line.strip_prefix("Cpus_allowed_list:")).map(str::trim).into();
    memory
}

// Single-thread fork shares only the already-complete, immutable public
// preprocessing pages. Each child subsequently reads exactly its own Shares.
unsafe extern "C" {
    fn fork()->i32;
    fn pipe(fds:*mut i32)->i32;
    fn close(fd:i32)->i32;
    fn dup2(old:i32,new:i32)->i32;
    fn waitpid(pid:i32,status:*mut i32,options:i32)->i32;
    fn kill(pid:i32,signal:i32)->i32;
    fn _exit(code:i32)->!;
}
struct ForkChild {pid:i32,reaped:bool}
impl ForkChild {
    fn id(&self)->u32 {self.pid as u32}
    fn kill(&mut self)->std::io::Result<()> {
        if self.reaped {return Ok(());}
        if unsafe{kill(self.pid,9)}<0 {return Err(std::io::Error::last_os_error());}Ok(())
    }
    fn wait(&mut self)->std::io::Result<std::process::ExitStatus> {
        if self.reaped {return Ok(std::process::ExitStatus::from_raw(0));}
        let mut status=0;
        loop {
            let r=unsafe{waitpid(self.pid,&mut status,0)};
            if r==self.pid {self.reaped=true;return Ok(std::process::ExitStatus::from_raw(status));}
            let e=std::io::Error::last_os_error();if e.kind()!=std::io::ErrorKind::Interrupted{return Err(e);}
        }
    }
}
struct ProcessWorker {
    child:ForkChild,
    input:Option<File>,
    output:Option<File>,
    ready:Value,
    final_memory:Value,
}
impl Drop for ProcessWorker {
    fn drop(&mut self) { let _=self.child.kill(); let _=self.child.wait(); }
}
impl ProcessWorker {
    fn new(out:&Path,id:usize,public:Arc<PublicPreprocessing>,previous_fds:&[i32])->Result<Self> {
        ensure!(fs::read_dir("/proc/self/task")?.count()==1,"public-only fork requires a single-thread parent");
        let mut up=[0;2];ensure!(unsafe{pipe(up.as_mut_ptr())}==0,"input pipe");
        let up_r=unsafe{File::from_raw_fd(up[0])};let up_w=unsafe{File::from_raw_fd(up[1])};
        let mut down=[0;2];ensure!(unsafe{pipe(down.as_mut_ptr())}==0,"output pipe");
        let down_r=unsafe{File::from_raw_fd(down[0])};let down_w=unsafe{File::from_raw_fd(down[1])};
        let pid=unsafe{fork()};ensure!(pid>=0,"fork worker");
        if pid==0 {
            unsafe {
                for &fd in previous_fds {close(fd);}
                if dup2(up_r.as_raw_fd(),0)<0 || dup2(down_w.as_raw_fd(),1)<0 {_exit(1);}
            }
            drop(up_r);drop(up_w);drop(down_r);drop(down_w);
            let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                crate::worker::run_stdio_with_public(id,out,public)));
            let code=match result {Ok(Ok(()))=>0,Ok(Err(e))=>{eprintln!("worker{id}: {e:#}");1},Err(_)=>1};
            unsafe{_exit(code)}
        }
        drop(up_r);drop(down_w);
        let mut worker=Self{child:ForkChild{pid,reaped:false},input:Some(up_w),output:Some(down_r),ready:Value::Null,final_memory:Value::Null};
        let ready=wire::receive(worker.output.as_mut().context("child stdout")?)?;
        ensure!(ready.starts_with(b"FSHEAP01"),"worker ready magic");
        worker.ready=serde_json::from_slice(&ready[8..])?;
        ensure!(worker.ready["id"].as_u64()==Some(id as u64),"worker ready party");
        ensure!(worker.ready["pid"].as_u64()==Some(worker.child.id() as u64),"worker ready pid");
        Ok(worker)
    }
    fn dispatch(&mut self,req:&[u8])->Result<(Vec<u8>,u64)> {
        let input=self.input.as_mut().context("child stdin")?;
        wire::send(input,req)?;input.flush()?;
        let output=self.output.as_mut().context("child stdout")?;
        let reply=wire::receive(output)?;
        let mut timing=[0;8];output.read_exact(&mut timing)?;
        if req[0]==wire::STOP {
            self.final_memory=serde_json::from_slice(&wire::receive(output)?)?;
            ensure!(self.child.wait()?.success(),"worker exited unsuccessfully after STOP");
        }
        Ok((reply,u64::from_le_bytes(timing)))
    }
}

enum Backend { Shared(Vec<Worker>), Processes(Vec<ProcessWorker>) }
#[derive(Serialize)]
struct Exchange {
    command:u8, coordinator_ns:u64, party_ns:Vec<u64>,
    backend_loop_ns:u64, simulator_overhead_ns:u64,
    request_bytes:Vec<usize>, response_bytes:Vec<usize>,
}
pub(crate) struct Simulation {
    backend:Backend, exchanges:Vec<Exchange>, checkpoint:Instant,
    active:bool, trace:PathBuf, ready_memory:Value,
}
impl Simulation {
    pub(crate) fn parties(&self)->usize {match &self.backend {Backend::Shared(w)=>w.len(),Backend::Processes(w)=>w.len()}}
    pub(crate) fn new(out:&Path,trace:&Path,public:Arc<PublicPreprocessing>,isolated:bool)->Result<Self> {
        let shape=Shape::read(out)?;
        let backend=if isolated {
            let mut workers:Vec<ProcessWorker>=Vec::new();
            for id in 0..shape.parties {
                let fds:Vec<i32>=workers.iter().flat_map(|w|[w.input.as_ref().unwrap().as_raw_fd(),w.output.as_ref().unwrap().as_raw_fd()]).collect();
                workers.push(ProcessWorker::new(out,id,Arc::clone(&public),&fds)?);
            }
            Backend::Processes(workers)
        } else {
            Backend::Shared((0..shape.parties).map(|id|Worker::with_preprocessing(id,out,Arc::clone(&public))).collect::<Result<Vec<_>>>()?)
        };
        let mut sim=Self{backend,exchanges:vec![],checkpoint:Instant::now(),active:false,trace:trace.into(),ready_memory:Value::Null};
        sim.ready_memory=sim.memory_snapshot();
        Ok(sim)
    }
    fn pids(&self)->Vec<u32> {match &self.backend {Backend::Shared(_)=>vec![],Backend::Processes(w)=>w.iter().map(|w|w.child.id()).collect()}}
    fn memory_snapshot(&self)->Value {
        let mut pids=vec![std::process::id()];pids.extend(self.pids());
        let samples=pids.into_iter().map(process_memory).collect::<Vec<_>>();
        let sum=if samples.iter().all(|v|v["rss_kb"].is_u64()) {Some(samples.iter().map(|v|v["rss_kb"].as_u64().unwrap()).sum::<u64>())} else {None};
        serde_json::json!({"scope":"sequential /proc samples at one barrier; observed current RSS sum counts shared public pages repeatedly; not peak or physical cluster RAM","processes":samples,"current_rss_sum_kb":sum})
    }
    pub(crate) fn metadata(&self)->Value {
        let (ready,final_memory)=match &self.backend {
            Backend::Shared(_)=>(vec![],vec![]),
            Backend::Processes(w)=>(w.iter().map(|w|w.ready.clone()).collect(),w.iter().map(|w|w.final_memory.clone()).collect()),
        };
        serde_json::json!({"backend":if matches!(self.backend,Backend::Shared(_)){"in-process-shared-heap"}else{"persistent-worker-processes"},
            "public_preprocessing_storage":if matches!(self.backend,Backend::Shared(_)){"shared Arc public tables; private allocations remain per worker"}else{"single-thread public-only fork/COW; private shares loaded independently in children"},
            "coordinator_pid":std::process::id(),"worker_process_ids":self.pids(),"worker_ready":ready,
            "ready_memory":self.ready_memory,"worker_final_memory":final_memory,
            "memory_scope":"per-process samples/high waters; never sum high waters as aggregate peak"})
    }
    pub(crate) fn begin(&mut self) {self.active=true;self.checkpoint=Instant::now();}
    pub(crate) fn exchange(&mut self,requests:&[Vec<u8>])->Result<Vec<Vec<u8>>> {
        ensure!(requests.len()==self.parties(),"simulation party count");
        ensure!(requests.iter().all(|r|!r.is_empty()),"empty simulated request");
        let coordinator_ns=self.checkpoint.elapsed().as_nanos() as u64;
        let mut responses=Vec::with_capacity(requests.len());
        let mut party_ns=Vec::with_capacity(requests.len());
        let start=Instant::now();
        match &mut self.backend {
            Backend::Shared(workers)=>for (worker,req) in workers.iter_mut().zip(requests) {
                let start=Instant::now();let reply=worker.dispatch(req[0],&req[1..])?;
                let elapsed=start.elapsed().as_nanos() as u64;
                responses.push(reply);party_ns.push(elapsed);
            },
            Backend::Processes(workers)=>for (worker,req) in workers.iter_mut().zip(requests) {
                let (reply,elapsed)=worker.dispatch(req)?;responses.push(reply);party_ns.push(elapsed);
            },
        }
        let backend_loop_ns=start.elapsed().as_nanos() as u64;
        let simulator_overhead_ns=backend_loop_ns.checked_sub(party_ns.iter().sum()).context("worker times exceed enclosing backend wall")?;
        if self.active {
            self.exchanges.push(Exchange{command:requests[0][0],coordinator_ns,party_ns,backend_loop_ns,simulator_overhead_ns,
                request_bytes:requests.iter().map(|x|x.len()+8).collect(),response_bytes:responses.iter().map(|x|x.len()+8).collect()});
        }
        self.checkpoint=Instant::now();Ok(responses)
    }
    pub(crate) fn finish(&mut self)->Result<()> {
        let coordinator_final_ns=self.checkpoint.elapsed().as_nanos() as u64;self.active=false;
        let mut trace=self.metadata();
        trace["schema"]="full-keccak-sequential-exchanges-v1".into();
        trace["parties"]=self.parties().into();
        trace["measurement"]="single-thread dispatch including state allocations/frees; IPC and loop overhead separate; no network wait".into();
        trace["exchanges"]=serde_json::to_value(&self.exchanges)?;
        trace["coordinator_final_ns"]=coordinator_final_ns.into();
        trace["online_end_memory"]=self.memory_snapshot();
        trace["private_payloads_recorded"]=false.into();
        fs::write(&self.trace,serde_json::to_vec_pretty(&trace)?)?;Ok(())
    }
}
