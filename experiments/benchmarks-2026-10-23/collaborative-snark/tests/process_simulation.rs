#![cfg(target_os = "linux")]

use std::{fs, path::{Path, PathBuf}, process::{Command, Stdio}, io::{Read, Write}};
use serde_json::Value;

const BIN: &str = env!("CARGO_BIN_EXE_ours-fullnet");
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!("sha-process-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&dir).unwrap();
        fs::write(dir.join("input.bin"), (0..400).map(|x|x as u8).collect::<Vec<_>>()).unwrap();
        Self(dir)
    }
    fn prepare(&self, name: &str) -> PathBuf {
        let out=self.0.join(name);
        ok(&["prepare","--input",self.0.join("input.bin").to_str().unwrap(),"--out",out.to_str().unwrap(),"--parties","8","--messages","2","--gamma","16","--tau","3","--development"]);
        out
    }
}
impl Drop for Fixture { fn drop(&mut self) { let _=fs::remove_dir_all(&self.0); } }
fn ok(args:&[&str]) { let o=Command::new(BIN).args(args).output().unwrap(); assert!(o.status.success(),"{args:?}: {}",String::from_utf8_lossy(&o.stderr)); }
fn json(p:&Path)->Value {serde_json::from_slice(&fs::read(p).unwrap()).unwrap()}
#[test]
fn complete_proofs_have_same_protocol_shapes_and_distinct_worker_heaps() {
    let f=Fixture::new(); let a=f.prepare("shared"); let b=f.prepare("isolated");
    for (out,isolate) in [(&a,false),(&b,true)] {
        let trace=out.join("trace.json");
        let mut args=vec!["simulate","--out",out.to_str().unwrap(),"--trace",trace.to_str().unwrap()];
        if isolate {args.push("--isolate-workers");}
        ok(&args); ok(&["verify","--out",out.to_str().unwrap()]);
    }
    assert_eq!(fs::read(a.join("statement.bin")).unwrap(),fs::read(b.join("statement.bin")).unwrap());
    assert_eq!(fs::read(a.join("key.bin")).unwrap(),fs::read(b.join("key.bin")).unwrap());
    let pa=fs::read(a.join("proof.bin")).unwrap(); let mut pb=fs::read(b.join("proof.bin")).unwrap();
    assert_eq!(pa.len(),pb.len()); assert_ne!(pa,pb);
    let ta=json(&a.join("trace.json")); let tb=json(&b.join("trace.json"));
    let pids=tb["worker_process_ids"].as_array().unwrap(); assert_eq!(pids.len(),8);
    let mut ids=pids.iter().map(|p|p.as_u64().unwrap()).collect::<Vec<_>>(); ids.sort();ids.dedup();assert_eq!(ids.len(),8);
    assert!(!pids.contains(&tb["coordinator_pid"]));
    assert_eq!(json(&b.join("prove.json"))["private_state_files_read_by_coordinator"],0);
    let ea=ta["exchanges"].as_array().unwrap();let eb=tb["exchanges"].as_array().unwrap();assert_eq!(ea.len(),eb.len());
    for (a,b) in ea.iter().zip(eb) {
        assert_eq!(a["command"],b["command"]);
        for k in ["request_bytes","response_bytes"] {
            if a["command"]==21 {
                let total=|x:&Value|x[k].as_array().unwrap().iter().map(|v|v.as_u64().unwrap()).sum::<u64>();
                assert_eq!(total(a),total(b));
            } else {assert_eq!(a[k],b[k]);}
        }
        for x in [a,b] {
            let sum:u64=x["party_ns"].as_array().unwrap().iter().map(|x|x.as_u64().unwrap()).sum();
            assert_eq!(x["backend_loop_ns"].as_u64().unwrap(),sum+x["simulator_overhead_ns"].as_u64().unwrap());
        }
    }
    pb[0]^=1;fs::write(b.join("proof.bin"),pb).unwrap();
    assert!(!Command::new(BIN).args(["verify","--out",b.to_str().unwrap()]).output().unwrap().status.success());
}
#[test]
fn invalid_child_command_exits_and_partial_startup_reaps_children() {
    let f=Fixture::new();let out=f.prepare("failure");
    let mut child=Command::new(BIN).args(["worker-stdio","--out",out.to_str().unwrap(),"--party","0"]).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().unwrap();
    let mut stdout=child.stdout.take().unwrap();let mut header=[0;8];stdout.read_exact(&mut header).unwrap();
    let mut ready=vec![0;u64::from_le_bytes(header) as usize];stdout.read_exact(&mut ready).unwrap();assert_eq!(&ready[..8],b"FSHEAP01");
    let mut stdin=child.stdin.take().unwrap();stdin.write_all(&1u64.to_le_bytes()).unwrap();stdin.write_all(&[255]).unwrap();stdin.flush().unwrap();
    assert!(!child.wait().unwrap().success());
    fs::remove_file(out.join("party-2.private")).unwrap();
    let o=Command::new(BIN).args(["simulate","--out",out.to_str().unwrap(),"--trace",out.join("bad.json").to_str().unwrap(),"--isolate-workers"]).output().unwrap();
    assert!(!o.status.success());
    let logs=String::from_utf8_lossy(&o.stderr);
    let ready=logs.lines().filter_map(|s|serde_json::from_str::<Value>(s).ok()).filter(|v|v["event"]=="ready").collect::<Vec<_>>();
    assert_eq!(ready.len(),2,"{logs}");
    for r in ready {assert!(!Command::new("kill").args(["-0",&r["pid"].to_string()]).stderr(Stdio::null()).status().unwrap().success());}
}

#[test]
fn killed_online_worker_fails_and_reaps_the_others() {
    use std::io::{BufRead,BufReader};
    use std::sync::{Arc,Mutex};
    let f=Fixture::new();let out=f.prepare("killed");
    let mut parent=Command::new(BIN).args(["simulate","--out",out.to_str().unwrap(),"--trace",out.join("bad.json").to_str().unwrap(),"--isolate-workers"])
        .stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    let pids=Arc::new(Mutex::new(Vec::<u64>::new()));let seen=Arc::clone(&pids);let err=parent.stderr.take().unwrap();
    let reader=std::thread::spawn(move||for line in BufReader::new(err).lines() {
        if let Ok(v)=serde_json::from_str::<Value>(&line.unwrap()) {if v["event"]=="ready" {seen.lock().unwrap().push(v["pid"].as_u64().unwrap());}}
    });
    let stdout=parent.stdout.take().unwrap();let mut killed=false;
    for line in BufReader::new(stdout).lines() {
        if let Ok(v)=serde_json::from_str::<Value>(&line.unwrap()) {if v["event"]=="online_start" {
            let pid=pids.lock().unwrap()[0];
            assert!(Command::new("kill").args(["-KILL",&pid.to_string()]).status().unwrap().success());killed=true;break;
        }}
    }
    assert!(killed);assert!(!parent.wait().unwrap().success());reader.join().unwrap();
    let pids=pids.lock().unwrap();assert_eq!(pids.len(),8);
    for pid in pids.iter() {assert!(!Command::new("kill").args(["-0",&pid.to_string()]).stderr(Stdio::null()).status().unwrap().success());}
}
