//! One global arbitrary-wiring binary R1CS. Never repeat it across packed slots.
mod circuit;
mod proof;
mod codec;
mod distributed;
mod public;
mod public_input;
mod sparse;
mod onehot;
pub use circuit::{Circuit,Task};

use anyhow::{Result, ensure};
use std::{fs,path::Path,time::Instant};

pub fn export_input(gates:usize,seed:u64,max_parties:usize,task:Task,out:&Path)->Result<()> {
    ensure!(!out.exists(),"use a fresh input directory");
    let circuit=Circuit::generate_task(gates,seed,max_parties,task)?;
    let mut rng=crate::prepare::entropy()?;let(witness,public)=circuit.witness(&mut rng);circuit.check(&witness,&public)?;
    let input:Vec<u8>=(0..circuit.inputs).map(|j|u8::from(witness[circuit.wire(j)])).collect();
    fs::create_dir_all(out)?;fs::write(out.join("circuit.json"),serde_json::to_vec_pretty(&circuit)?)?;
    fs::write(out.join("input.private"),input)?;fs::write(out.join("statement.json"),serde_json::to_vec(&public)?)?;Ok(())
}

pub fn run(constraints:usize,seed:u64,max_parties:usize,parties:usize,task:Task,input:Option<&Path>,trace:Option<&Path>,gamma:usize,tau:usize,index_block_bits:usize,out:&Path)->Result<()> {
    ensure!(!out.exists(),"use a fresh general-circuit output directory");
    let _encoding=crate::code::sequential_encoding();
    let source_started=Instant::now();
    let circuit=Circuit::generate_task(constraints,seed,max_parties,task)?;
    let mut rng=crate::prepare::entropy()?;
    let (witness,public)=if let Some(input)=input {
        let bits=fs::read(input)?;ensure!(bits.iter().all(|&v|v<=1),"input bytes must be bits");
        circuit.witness_with_inputs(&bits.into_iter().map(|v|v!=0).collect::<Vec<_>>(),&mut rng)?
    }else{circuit.witness(&mut rng)};
    circuit.check(&witness,&public)?;
    let source_preparation_seconds=source_started.elapsed().as_secs_f64();
    let started=Instant::now();
    let cfg=proof::Config::new_block(&circuit,parties,gamma,tau,index_block_bits).map_err(anyhow::Error::msg)?;
    let parameters=cfg.parameter_record();
    eprintln!("GENERAL_PUBLIC_INDEX_READY");
    distributed::pin_compute_thread();
    let setup_seconds=started.elapsed().as_secs_f64();let started=Instant::now();
    if let Some(path)=trace {ensure!(!path.exists(),"use a fresh trace directory");crate::execution_trace::start(parties);}
    let proof=proof::prove(&cfg,&circuit,&witness,&public,&mut rng);
    let proof_bytes=codec::encode_proof(&proof);
    let trace_summary=if let Some(path)=trace {crate::execution_trace::finish(path)?;Some(serde_json::from_slice::<serde_json::Value>(&fs::read(path.join("manifest.json"))?)?)}else{None};
    if let Some(t)=&trace_summary {ensure!(t["challenges"]==parameters["expected_challenge_stages"],"complete trace challenge count differs from protocol");}
    let prove_control_seconds=started.elapsed().as_secs_f64();
    let worker_stats=cfg.actor_stats();
    let key_bytes=codec::encode_key(&cfg.verifier_key());
    let key=codec::decode_key(&key_bytes).map_err(anyhow::Error::msg)?;
    let decoded=codec::decode_proof(&key,&proof_bytes).map_err(anyhow::Error::msg)?;
    let started=Instant::now();proof::verify(&key,&public,&decoded).map_err(anyhow::Error::msg)?;
    let verify_seconds=started.elapsed().as_secs_f64();
    fs::create_dir_all(out)?;
    fs::write(out.join("circuit.json"),serde_json::to_vec_pretty(&circuit)?)?;
    fs::write(out.join("witness.private"),witness.iter().map(|&b|u8::from(b)).collect::<Vec<_>>())?;
    fs::write(out.join("verifier-key.bin"),key_bytes)?;
    fs::write(out.join("proof.bin"),&proof_bytes)?;
    fs::write(out.join("statement.json"),serde_json::to_vec(&public)?)?;
    let record=serde_json::json!({"status":"complete-proof-sharded-public-control","proof_generated":true,
        "task":task,"logical_gates":constraints,"raw_logical_constraints":circuit.raw_rows(),"padded_constraints":circuit.rows(),
        "padded_witness_bits":circuit.bits(),"parties":parties,"public":public,
        "cross_slot_entries":circuit.cross_slot_entries(parties)?,"proof_bytes":proof_bytes.len(),
        "verified_after_decode":true,"fresh_conversions":3,"public_work":"owner-sharded-kernels-with-bounded-public-coordinator-tails",
        "public_sorting":"fixed-index-preprocessing", "public_input_authentication":"six-fixed-columns-one-batch-opening", "proof_format":"GENPRF05", "public_tail_factor_cell_floor":1024,"public_product_boundary_cell_floor":public::PRODUCT_BOUNDARY_CELLS,"public_tail_policy":"max(floor,initial-layer-cells/N)","public_pcs_tail_cell_floor":4096,"public_gather_per_owner_limit":4096,"private_matrix_authentication":"onehot-blocks-single-binary-PCS","index_block_bits":index_block_bits,
        "packed_slots":parties/4,"rows_per_party":circuit.rows()/(parties/4),
        "witness_bits_per_party":circuit.bits()/(parties/4),"gamma":gamma,"tau":tau,
        "source_preparation_wall_seconds":source_preparation_seconds,
        "parameters":parameters,
        "measurement_compute_cpu":std::env::var("GENERAL_COMPUTE_CPU").ok(),
        "trace":trace_summary,
        "index_setup_wall_seconds":setup_seconds,"prove_control_wall_seconds":prove_control_seconds,
        "verify_wall_seconds":verify_seconds,"actor_stats":worker_stats,
        "actor_stats_scope":"public kernels and private SC2 share residency/arithmetic; excludes original private PCS backend and client preparation",
        "communication_scope":"public peer packets including framing; excludes controller commands, reductions and original private PCS traffic",
        "timing_scope":"single-host correctness control; prove includes ideal preparation and all public authentication"});
    fs::write(out.join("control.json"),serde_json::to_vec_pretty(&record)?)?;
    println!("{record}");
    Ok(())
}

/// Independent verification reads no circuit or private witness file.
pub fn verify_files(out:&Path)->Result<()> {
    let key=codec::decode_key(&fs::read(out.join("verifier-key.bin"))?).map_err(anyhow::Error::msg)?;
    let proof=codec::decode_proof(&key,&fs::read(out.join("proof.bin"))?).map_err(anyhow::Error::msg)?;
    let public=serde_json::from_slice(&fs::read(out.join("statement.json"))?)?;
    proof::verify(&key,&public,&proof).map_err(anyhow::Error::msg)?;
    println!("general proof verified");Ok(())
}
