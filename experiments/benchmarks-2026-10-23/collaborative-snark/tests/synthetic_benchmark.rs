use ours_fullnet::{application::Application, coordinator, prepare::{self, Shape}, wire};
use serde_json::Value;
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);
impl Drop for Fixture { fn drop(&mut self) { let _=fs::remove_dir_all(&self.0); } }

fn work_shape(trace: &Value) -> Vec<(u64,u64,u64)> {
    trace["exchanges"].as_array().unwrap().iter().map(|e| (
        e["command"].as_u64().unwrap(),
        e["request_bytes"].as_array().unwrap().iter().map(|v|v.as_u64().unwrap()).sum(),
        e["response_bytes"].as_array().unwrap().iter().map(|v|v.as_u64().unwrap()).sum(),
    )).collect()
}

#[test]
fn synthetic_benchmark_matches_real_online_work_shapes_without_share_files() {
    let root=std::env::temp_dir().join(format!("synthetic-benchmark-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
    fs::create_dir(&root).unwrap(); let fixture=Fixture(root);
    let shape=Shape { application:Application::Keccak, layout_version:prepare::LAYOUT_VERSION,
        parties:8, messages:2, gamma:16, tau:3, development:true };
    let input=fixture.0.join("input.bin");
    fs::write(&input,(0..400).map(|x|x as u8).collect::<Vec<_>>()).unwrap();
    let real=fixture.0.join("real"); let real_trace=fixture.0.join("real-trace.json");
    prepare::run(shape.clone(),&input,&real).unwrap();
    coordinator::simulate(&real,&real_trace).unwrap();
    coordinator::verify(&real).unwrap();
    let statement=fs::read(real.join("statement.bin")).unwrap();
    let mut bad=statement.clone(); bad[0]^=1;
    fs::write(real.join("statement.bin"),bad).unwrap();
    assert!(coordinator::verify(&real).is_err());
    fs::write(real.join("statement.bin"),statement).unwrap();
    coordinator::verify(&real).unwrap();

    let synthetic=fixture.0.join("synthetic"); let trace=fixture.0.join("synthetic-trace.json");
    let command=Command::new(env!("CARGO_BIN_EXE_ours-fullnet")).args([
        "benchmark","--parties","8","--messages","2","--gamma","16","--tau","3","--development",
        "--out",synthetic.to_str().unwrap(),"--trace",trace.to_str().unwrap(),
    ]).output().unwrap();
    assert!(command.status.success(),"{}",String::from_utf8_lossy(&command.stderr));
    let record:Value=serde_json::from_slice(&fs::read(synthetic.join("prove.json")).unwrap()).unwrap();
    let prep:Value=serde_json::from_slice(&fs::read(synthetic.join("preparation.json")).unwrap()).unwrap();
    let synthetic_trace:Value=serde_json::from_slice(&fs::read(&trace).unwrap()).unwrap();
    let real_trace:Value=serde_json::from_slice(&fs::read(real_trace).unwrap()).unwrap();
    assert_eq!(work_shape(&real_trace),work_shape(&synthetic_trace));
    assert_eq!(work_shape(&synthetic_trace).first().unwrap().0,wire::START as u64);
    assert_eq!(work_shape(&synthetic_trace).last().unwrap().0,wire::PCS_QUERIES as u64);
    assert_eq!(fs::metadata(real.join("proof.bin")).unwrap().len(),fs::metadata(synthetic.join("benchmark-transcript.bin")).unwrap().len());
    assert_eq!(record["phase"],"online_kernel_benchmark");
    assert_eq!(record["synthetic_shares"],true);
    assert_eq!(record["verification_status"],"not_applicable_synthetic_shares");
    assert_eq!(record["private_state_files_read_by_coordinator"],0);
    if cfg!(target_os="linux") {
        assert_eq!(record["simulation_backend"]["backend"],"persistent-worker-processes");
        let pids=synthetic_trace["worker_process_ids"].as_array().unwrap();
        let mut ids=pids.iter().map(|p|p.as_u64().unwrap()).collect::<Vec<_>>();
        ids.sort();ids.dedup();assert_eq!(ids.len(),8);
        assert!(!pids.contains(&synthetic_trace["coordinator_pid"]));
        for worker in synthetic_trace["worker_ready"].as_array().unwrap() {
            assert_eq!(worker["private_state_files_read"],0);
            assert_eq!(worker["synthetic_shares"],true);
        }
    } else {assert_eq!(record["simulation_backend"]["backend"],"in-process-shared-heap");}
    assert!(!record["algebraic_check_failures"].as_array().unwrap().is_empty());
    assert!(record.get("proof_bytes").is_none());
    assert_eq!(synthetic_trace["synthetic_shares"],true);
    assert_eq!(prep["private_share_files_written"],0);
    assert!(!synthetic.join("proof.bin").exists());
    assert!(!fs::read_dir(&synthetic).unwrap().any(|p|p.unwrap().path().extension().is_some_and(|s|s=="private")));
    assert!(coordinator::verify(&synthetic).is_err());
    assert!(ours_fullnet::benchmark::run(shape,&synthetic,&trace).is_err());
}
