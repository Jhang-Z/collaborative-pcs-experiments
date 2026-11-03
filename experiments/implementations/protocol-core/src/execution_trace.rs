//! Opt-in logical-actor CPU/message trace. Inactive proofs retain their original path.
//! Clock intervals use the calling thread's CPU clock; recorder work and explicitly paused
//! transport are excluded. N prover actors plus coordinator actor N are recorded separately.
use std::{cell::RefCell,fs,io,path::Path,sync::{Arc,Mutex,OnceLock,atomic::{AtomicBool,AtomicU64,Ordering}}};

static ACTIVE:AtomicBool=AtomicBool::new(false);
static NEXT_SESSION:AtomicU64=AtomicU64::new(1);
static SESSION:OnceLock<Mutex<Option<Arc<Session>>>>=OnceLock::new();
const PRIVATE_GATHER:u64=1;
const PRIVATE_BROADCAST:u64=2;

#[derive(Clone)]
enum Event {Compute(u64),Send{peer:usize,tag:u64,bytes:usize,nonblocking:bool},Recv{peer:usize,tag:u64,bytes:usize},Challenge,End}
struct Session {id:u64,n:usize,events:Vec<Mutex<Vec<Event>>>,challenges:AtomicU64,recorder_cpu_ns:AtomicU64}
struct Context {role:Option<usize>,allowed:bool,session:u64,last:Option<u64>}
thread_local! {static CONTEXT:RefCell<Context>=const{RefCell::new(Context{role:None,allowed:true,session:0,last:None})};}

#[derive(Debug)]
pub struct Summary {pub parties:usize,pub actors:usize,pub challenges:u64,pub compute_ns:Vec<u64>,pub sent_bytes:Vec<u64>,pub recorder_cpu_ns:u64}

fn cpu_ns()->u64 {
    let mut t=libc::timespec{tv_sec:0,tv_nsec:0};
    let status=unsafe{libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID,&mut t)};
    assert_eq!(status,0,"CLOCK_THREAD_CPUTIME_ID");
    (t.tv_sec as u64).checked_mul(1_000_000_000).unwrap()+t.tv_nsec as u64
}
fn session()->Option<Arc<Session>> {
    if !ACTIVE.load(Ordering::Acquire){return None;}
    SESSION.get().unwrap().lock().unwrap().clone()
}
pub fn recording()->bool {ACTIVE.load(Ordering::Acquire)}
pub fn enabled()->bool {recording()&&CONTEXT.with(|c|c.borrow().allowed)}
pub fn coordinator()->usize {session().expect("trace session").n}
pub fn current_rank()->usize {let s=session().expect("trace session");CONTEXT.with(|c|c.borrow().role.unwrap_or(s.n))}

/// Starts one recording. Source/index preparation can immediately enter pause().
pub fn start(n:usize) {
    assert!(n>0);let cell=SESSION.get_or_init(||Mutex::new(None));let mut lock=cell.lock().unwrap();assert!(lock.is_none(),"trace already recording");
    let id=NEXT_SESSION.fetch_add(1,Ordering::Relaxed);
    *lock=Some(Arc::new(Session{id,n,events:(0..=n).map(|_|Mutex::new(Vec::new())).collect(),challenges:AtomicU64::new(0),recorder_cpu_ns:AtomicU64::new(0)}));
    CONTEXT.with(|c|{let mut c=c.borrow_mut();c.session=id;c.last=Some(cpu_ns());});
    ACTIVE.store(true,Ordering::Release);
}
/// Flush user arithmetic to its logical actor and reset the anchor after recorder work.
pub fn flush_compute() {
    if !recording(){return;}
    let now=cpu_ns();let Some(s)=session()else{return;};
    let value=CONTEXT.with(|c|{let mut c=c.borrow_mut();
        if c.session!=s.id {c.session=s.id;c.last=Some(now);return None;}
        let rank=c.role.unwrap_or(s.n);assert!(rank<=s.n);
        let elapsed=c.last.map_or(0,|last|now.saturating_sub(last));
        c.last=Some(now);(c.allowed&&elapsed>0).then_some((rank,elapsed))
    });
    if let Some((rank,elapsed))=value{s.events[rank].lock().unwrap().push(Event::Compute(elapsed));}
    let end=cpu_ns();CONTEXT.with(|c|c.borrow_mut().last=Some(end));s.recorder_cpu_ns.fetch_add(end.saturating_sub(now),Ordering::Relaxed);
}
fn event(rank:usize,event:Event) {
    if !enabled(){return;}
    flush_compute();let start=cpu_ns();let Some(s)=session()else{return;};assert!(rank<=s.n);
    if matches!(event,Event::Challenge){s.challenges.fetch_add(1,Ordering::Relaxed);}
    s.events[rank].lock().unwrap().push(event);
    let end=cpu_ns();CONTEXT.with(|c|c.borrow_mut().last=Some(end));s.recorder_cpu_ns.fetch_add(end.saturating_sub(start),Ordering::Relaxed);
}
pub struct ScopeGuard {old:Option<usize>}
pub fn scope(rank:usize)->ScopeGuard {
    flush_compute();let old=CONTEXT.with(|c|{let mut c=c.borrow_mut();let old=c.role;c.role=Some(rank);c.last=recording().then(cpu_ns);old});ScopeGuard{old}
}
impl Drop for ScopeGuard {fn drop(&mut self){flush_compute();CONTEXT.with(|c|{let mut c=c.borrow_mut();c.role=self.old;c.last=recording().then(cpu_ns);});}}
pub struct ModeGuard {old:bool}
fn mode(allowed:bool)->ModeGuard {
    flush_compute();let old=CONTEXT.with(|c|{let mut c=c.borrow_mut();let old=c.allowed;c.allowed=allowed;c.last=recording().then(cpu_ns);old});ModeGuard{old}
}
/// Thread-local. Actor dispatch must propagate enabled() explicitly to its worker task.
pub fn pause()->ModeGuard {mode(false)}
/// Overrides an outer pause for an online commitment; an inner pause still excludes IPC.
pub fn force_online()->ModeGuard {mode(true)}
impl Drop for ModeGuard {fn drop(&mut self){flush_compute();CONTEXT.with(|c|{let mut c=c.borrow_mut();c.allowed=self.old;c.last=recording().then(cpu_ns);});}}

/// bytes is the full serialized application message, including caller-specified framing.
pub fn send(src:usize,dst:usize,tag:u64,bytes:usize,nonblocking:bool) {event(src,Event::Send{peer:dst,tag,bytes,nonblocking});}
pub fn recv(src:usize,dst:usize,tag:u64,bytes:usize) {event(dst,Event::Recv{peer:src,tag,bytes});}
/// Existing transport's Vec messages use its 8-byte length prefix.
pub fn gather(sizes:&[usize]) {
    batch(sizes.iter().copied(),true);
}
pub fn scatter(sizes:&[usize]) {
    batch(sizes.iter().copied(),false);
}
fn batch(sizes:impl ExactSizeIterator<Item=usize>,up:bool) {
    if !enabled(){return;}flush_compute();let start=cpu_ns();let s=session().unwrap();assert_eq!(sizes.len(),s.n);
    for(rank,size)in sizes.enumerate(){let bytes=size.checked_add(8).unwrap();let(src,dst,tag)=if up{(rank,s.n,PRIVATE_GATHER)}else{(s.n,rank,PRIVATE_BROADCAST)};
        s.events[src].lock().unwrap().push(Event::Send{peer:dst,tag,bytes,nonblocking:true});
        s.events[dst].lock().unwrap().push(Event::Recv{peer:src,tag,bytes});
    }
    let end=cpu_ns();CONTEXT.with(|c|c.borrow_mut().last=Some(end));s.recorder_cpu_ns.fetch_add(end.saturating_sub(start),Ordering::Relaxed);
}
pub fn broadcast(payload_bytes:usize) {if !enabled(){return;}batch(std::iter::repeat_n(payload_bytes,coordinator()),false);}
pub fn record_challenge() {if !enabled(){return;}event(current_rank(),Event::Challenge);}

fn event_json(e:&Event)->String {match e {
    Event::Compute(ns)=>format!("{{\"op\":\"compute\",\"compute_ns\":{ns}}}"),
    Event::Send{peer,tag,bytes,nonblocking}=>format!("{{\"op\":\"{}\",\"compute_ns\":0,\"peer\":{peer},\"tag\":{tag},\"bytes\":{bytes}}}",if *nonblocking{"isend"}else{"send"}),
    Event::Recv{peer,tag,bytes}=>format!("{{\"op\":\"recv\",\"compute_ns\":0,\"peer\":{peer},\"tag\":{tag},\"bytes\":{bytes}}}"),
    Event::Challenge=>"{\"op\":\"challenge\",\"compute_ns\":0}".into(),
    Event::End=>"{\"op\":\"end\",\"compute_ns\":0}".into(),
}}
/// Call after all online actors have joined their last task. Serialization is outside clocks.
pub fn finish(directory:impl AsRef<Path>)->io::Result<Summary> {
    flush_compute();ACTIVE.store(false,Ordering::Release);
    let s=SESSION.get().expect("trace not started").lock().unwrap().take().expect("trace not started");
    let directory=directory.as_ref();fs::create_dir_all(directory)?;
    let mut compute_ns=vec![0;s.n+1];let mut sent_bytes=vec![0;s.n+1];
    for(rank,buffer)in s.events.iter().enumerate(){let mut events=buffer.lock().unwrap();events.push(Event::End);
        let mut output=format!("{{\"schema\":\"collaborative-actor-cpu-v2\",\"rank\":{rank},\"parties\":{},\"actors\":{},\"coordinator\":{},\"clock\":\"CLOCK_THREAD_CPUTIME_ID\"}}\n",s.n,s.n+1,s.n);
        for e in events.iter(){match e{Event::Compute(ns)=>compute_ns[rank]+=ns,Event::Send{bytes,..}=>sent_bytes[rank]+=*bytes as u64,_=>{}}output.push_str(&event_json(e));output.push('\n');}
        fs::write(directory.join(format!("rank-{rank:04}.jsonl")),output)?;
    }
    let summary=Summary{parties:s.n,actors:s.n+1,challenges:s.challenges.load(Ordering::Relaxed),compute_ns,sent_bytes,recorder_cpu_ns:s.recorder_cpu_ns.load(Ordering::Relaxed)};
    let nums=|v:&[u64]|v.iter().map(u64::to_string).collect::<Vec<_>>().join(",");
    fs::write(directory.join("manifest.json"),format!("{{\"schema\":\"collaborative-actor-cpu-v2\",\"parties\":{},\"actors\":{},\"coordinator\":{},\"challenges\":{},\"compute_ns\":[{}],\"sent_bytes\":[{}],\"recorder_cpu_ns\":{},\"clock\":\"CLOCK_THREAD_CPUTIME_ID\",\"coordinator_colocated_with\":0}}\n",summary.parties,summary.actors,summary.parties,summary.challenges,nums(&summary.compute_ns),nums(&summary.sent_bytes),summary.recorder_cpu_ns))?;
    Ok(summary)
}

#[cfg(test)]mod tests {
    use super::*;
    #[test]fn scopes_pause_and_logical_messages_are_recorded_without_sockets(){
        // A recorder is process-wide; ordinary proof tests must not join this fixture.
        if std::env::var_os("B2_TRACE_FIXTURE_CHILD").is_none(){
            let out=std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact","execution_trace::tests::scopes_pause_and_logical_messages_are_recorded_without_sockets","--nocapture"])
                .env("B2_TRACE_FIXTURE_CHILD","1").output().unwrap();
            assert!(out.status.success()&&String::from_utf8_lossy(&out.stdout).contains("1 passed;"),"{}{}",String::from_utf8_lossy(&out.stdout),String::from_utf8_lossy(&out.stderr));return;
        }
        let out=std::env::temp_dir().join(format!("b2-execution-trace-{}",std::process::id()));let _=fs::remove_dir_all(&out);
        start(2);{let _offline=pause();{let _p=scope(1);std::hint::black_box((0..1000u64).sum::<u64>());send(1,2,99,999,true);record_challenge();}{let _online=force_online();let _p=scope(0);std::hint::black_box((0..1000u64).sum::<u64>());}}
        gather(&[32,64]);broadcast(16);record_challenge();let summary=finish(&out).unwrap();
        assert_eq!(summary.challenges,1);assert_eq!(summary.sent_bytes,[40,72,48]);
        assert!(summary.compute_ns[0]>0);assert_eq!(summary.compute_ns[1],0);let text=fs::read_to_string(out.join("rank-0000.jsonl")).unwrap();assert!(text.contains("\"op\":\"isend\""));assert!(text.contains("\"op\":\"recv\""));
        fs::remove_dir_all(&out).unwrap();assert!(!recording());

        // Exercise the real private-PCS transport and FS hooks without WIRE/TCP.
        use crate::field::{Field,L};
        start(2);let mut states=vec![0u64;2];crate::parallel::parties(&mut states,|i,x|{*x=std::hint::black_box(i as u64+7);});assert_eq!(states,[7,8]);
        assert_eq!(crate::transport::values(vec![vec![1u64,2],vec![3]],true),vec![vec![1,2],vec![3]]);
        crate::transport::arrays(vec![[L::ONE];2]);crate::transport::hashes(vec![[0;32];2]);
        let op0=crate::protocol::Opening{values:[L::ONE;2],salt:[0;32],path:vec![[0;32]]};let mut op1=op0.clone();op1.path.clear();
        let opened=crate::transport::openings(vec![vec![op0],vec![op1]],&[(0,0),(1,0)],2);assert_eq!(opened[0][0].path.len(),1);
        crate::transport::broadcast(b"abc");
        let hasher=crate::merkle::Hasher::<binius_hash::Blake3HashSuite>::default();let mut transcript=crate::fs::Transcript::new(&hasher,b"trace fixture");transcript.round(&[0;32],b"stage").field();
        let summary=finish(&out).unwrap();assert_eq!(summary.sent_bytes,[240,200,102]);assert_eq!(summary.challenges,1);assert!(summary.compute_ns[..2].iter().all(|&ns|ns>0));fs::remove_dir_all(out).unwrap();
    }
}
