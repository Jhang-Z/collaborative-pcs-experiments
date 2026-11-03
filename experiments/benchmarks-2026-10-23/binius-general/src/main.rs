mod timing;
use std::{fs, path::PathBuf, sync::{Arc, Mutex}, time::Instant};
use anyhow::{ensure, Result};
use binius_core::{constraint_system::ValueVec, word::Word};
use binius_frontend::{Circuit, CircuitBuilder, Options, Wire};
use binius_hash::sha256::Sha256HashSuite;
use binius_prover::{OptimalPackedB128, zk_config::ZKProver};
use binius_verifier::{config::StdChallenger, transcript::{ProverTranscript, VerifierTranscript}, zk_config::ZKVerifier};
use clap::Parser;
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest, Sha256};
type Prover = ZKProver<OptimalPackedB128, Sha256HashSuite>;
type Verifier = ZKVerifier<Sha256HashSuite>;
#[derive(Parser)]
struct Args {
    #[arg(long)] graph: PathBuf,
    #[arg(long)] input: Option<PathBuf>,
    #[arg(long)] out: PathBuf,
    #[arg(long, default_value="native-default")] mode: String,
    #[arg(long, default_value_t=3)] runs: usize,
    #[arg(long)] verify_only: bool,
    #[arg(long)] single: bool,
}
#[derive(Deserialize)]
struct Graph { format: String, task: String, inputs: usize, gates: Vec<Gate> }
#[derive(Deserialize)]
struct Gate { left: Vec<usize>, right: u64 }
fn hash(bytes: &[u8]) -> String { Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect() }
fn build(g: &Graph, mode: &str) -> Result<(Circuit, Vec<Wire>, Wire)> {
    ensure!(g.format == "general-binary-feedback-v1", "unexpected graph format");
    ensure!(["linear_feedback", "xor_and_random", "xor_and_random50"].contains(&g.task.as_str()), "unexpected task");
    ensure!(!g.gates.is_empty() && g.inputs > 0, "empty graph");
    let mut opts = Options::default();
    if mode == "preserved-graph" {
        opts.enable_gate_fusion = false;
        opts.enable_common_subexpression_elimination = false;
        opts.enable_dead_code_elimination = false;
        opts.enable_algebraic_folding = false;
        opts.enable_zero_propagation = false;
    } else { ensure!(mode == "native-default", "unknown compilation mode"); }
    let b = CircuitBuilder::with_opts(opts);
    let inputs: Vec<_> = (0..g.inputs).map(|_| b.add_witness()).collect();
    for &w in &inputs { b.assert_zero("boolean_input", b.shr(w, 1)); }
    let mut wires = inputs.clone();
    for gate in &g.gates {
        ensure!(gate.left.iter().all(|&i| i < wires.len()), "forward XOR reference");
        ensure!((1..=3).contains(&gate.left.len()), "invalid XOR fan-in");
        let args:Vec<_>=gate.left.iter().map(|&i|wires[i]).collect();
        let mut v = if args.len()==1 {args[0]}else{b.bxor_multi(&args)};
        if gate.right != u64::MAX {
            ensure!((gate.right as usize) < wires.len(), "forward AND reference");
            v = b.band(v, wires[gate.right as usize]);
        }
        wires.push(v);
    }
    let out = b.add_inout(); b.assert_eq("public_output", *wires.last().unwrap(), out);
    let c = b.build(); ensure!(c.inout() == [out], "unexpected public ordering");
    Ok((c, inputs, out))
}
fn evaluate(g: &Graph, input: &[u8]) -> Result<u64> {
    ensure!(input.len() == g.inputs && input.iter().all(|&b| b <= 1), "expected one byte per Boolean input");
    let mut w = input.to_vec();
    for gate in &g.gates {
        let mut v = gate.left.iter().fold(0, |a, &i| a ^ w[i]);
        if gate.right != u64::MAX { v &= w[gate.right as usize]; }
        w.push(v);
    }
    Ok(*w.last().unwrap() as u64)
}
fn fill(c: &Circuit, inputs: &[Wire], out: Wire, input: &[u8], public: u64) -> Result<ValueVec> {
    let mut w = c.new_witness_filler();
    for (&wire, &value) in inputs.iter().zip(input) { w[wire] = Word(value as u64); }
    w[out] = Word(public); c.populate_wire_witness(&mut w)?;
    let w = w.into_value_vec(); c.constraint_system().verify(&w)?; Ok(w)
}
fn check(v: &Verifier, public: u64, proof: Vec<u8>) -> Result<()> {
    let mut t = VerifierTranscript::new(StdChallenger::default(), proof);
    v.verify(&[Word(public)], &mut t)?; t.finalize()?; Ok(())
}
fn main() -> Result<()> {
    let a = Args::parse();
    ensure!(binius_utils::rayon::current_num_threads() == 1, "requires single core/thread");
    let graph_bytes = fs::read(&a.graph)?;
    let g: Graph = serde_json::from_slice(&graph_bytes)?;
    if a.verify_only {
        let manifest: serde_json::Value = serde_json::from_slice(&fs::read(a.out.join("result.json"))?)?;
        ensure!(manifest["graph_sha256"] == hash(&graph_bytes) && manifest["mode"] == a.mode, "wrong graph or mode");
        let start = Instant::now(); let (c, _, _) = build(&g, &a.mode)?;
        let v = Verifier::setup(c.constraint_system().clone(), 1)?;
        let setup_s = start.elapsed().as_secs_f64();
        let public = manifest["public_output"].as_u64().unwrap();
        let proof = fs::read(a.out.join("proof.bin"))?;
        let start = Instant::now(); check(&v, public, proof.clone())?;
        let verify_s = start.elapsed().as_secs_f64();
        ensure!(check(&v, public ^ 1, proof.clone()).is_err(), "wrong public output accepted");
        let mut corrupted = proof; let k = corrupted.len() / 2; corrupted[k] ^= 1;
        ensure!(check(&v, public, corrupted).is_err(), "corrupted proof accepted");
        let r = json!({"public_only_accept":true,"wrong_output_rejected":true,"mutated_proof_rejected":true,"setup_s":setup_s,"verify_s":verify_s});
        fs::write(a.out.join("independent-verify.json"), serde_json::to_vec_pretty(&r)?)?;
        println!("{r}"); return Ok(());
    }
    ensure!(a.runs > 0, "runs must be positive"); fs::create_dir_all(&a.out)?;
    let input = fs::read(a.input.as_ref().expect("--input required for proving"))?;
    let start = Instant::now(); let (c, inputs, out) = build(&g, &a.mode)?;
    let circuit_s = start.elapsed().as_secs_f64();
    let cs = c.constraint_system();
    let shape = json!({"public_words":cs.n_inout,"private_words":cs.n_private,"and_constraints":cs.and_constraints.len(),"zero_constraints":cs.zero_constraints.len(),"imul_constraints":cs.imul_constraints.len(),"bmul_constraints":cs.bmul_constraints.len()});
    let start = Instant::now(); let public = evaluate(&g, &input)?;
    let witness = fill(&c, &inputs, out, &input, public)?;
    let witness_s = start.elapsed().as_secs_f64();
    // Prove that the input range constraint exists, not merely a parser check.
    let mut bad = input.clone(); bad[0] = 2;
    ensure!(fill(&c, &inputs, out, &bad, public).is_err(), "non-Boolean input accepted by native constraints");
    let start = Instant::now(); let v = Verifier::setup(cs.clone(), 1)?;
    let p = Prover::setup(&v)?; let setup_s = start.elapsed().as_secs_f64();
    let mut records = vec![]; let mut last_proof = vec![];
    // One warm-up, then alternating profiled/unprofiled fresh proofs.
    for iteration in 0..if a.single {1}else{1+a.runs*2} {
        let profiled = iteration > 0 && iteration % 2 == 1;
        let state = Arc::new(Mutex::new(timing::State::new()));
        let subscriber = timing::Timings(state.clone());
        let run = || -> Result<Vec<u8>> {
            *state.lock().unwrap() = timing::State::new();
            let mut t = ProverTranscript::new(StdChallenger::default()); let mut rng = rand::rng();
            p.prove(&witness, &mut rng, &mut t)?; let proof = t.finalize();
            state.lock().unwrap().finish(); Ok(proof)
        };
        let proof = if profiled { tracing::subscriber::with_default(subscriber, run)? } else { run()? };
        let start = Instant::now(); check(&v, public, proof.clone())?;
        let verify_s = start.elapsed().as_secs_f64();
        let s = state.lock().unwrap();
        let phases: serde_json::Map<String,serde_json::Value> = timing::NAMES.iter().enumerate().map(|(i,&name)| (name.into(), json!({"wall_s":s.wall[i],"cpu_s":s.cpu[i]}))).collect();
        let record = json!({"iteration":iteration,"warmup":!a.single&&iteration==0,"profiled":profiled,"online_s":s.wall.iter().sum::<f64>(),"online_cpu_s":s.cpu.iter().sum::<f64>(),"verify_s":verify_s,"proof_bytes":proof.len(),"phases":phases});
        println!("{record}"); records.push(record); last_proof = proof;
    }
    fs::write(a.out.join("proof.bin"), &last_proof)?;
    let r = json!({"upstream_commit":"4428e759dd27956bd5b9ae5025d67eb8ccc1accf","mode":a.mode,"task":g.task,"logical_nodes":g.gates.len(),"logical_xor_gates":g.gates.iter().map(|x|x.left.len()-1).sum::<usize>(),"logical_and_nodes":g.gates.iter().filter(|x| x.right!=u64::MAX).count(),"private_input_bits":g.inputs,"public_output":public,"graph_sha256":hash(&graph_bytes),"input_sha256":hash(&input),"proof_sha256":hash(&last_proof),"native_constraints":shape,"circuit_s":circuit_s,"witness_and_constraint_check_s":witness_s,"public_prover_verifier_setup_s":setup_s,"parameters":{"log_inv_rate":1,"hash_suite":"SHA256","native_query_security_bits":binius_verifier::SECURITY_BITS,"threads":1,"zero_knowledge":true},"records":records});
    fs::write(a.out.join("result.json"), serde_json::to_vec_pretty(&r)?)?; Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn binary_random50_relation() -> Result<()> {
        for right in [u64::MAX,1] {
            let left=if right==u64::MAX{vec![0,1]}else{vec![0]};
            let g=Graph{format:"general-binary-feedback-v1".into(),task:"xor_and_random50".into(),inputs:2,gates:vec![Gate{left,right}]};
            for mode in ["native-default","preserved-graph"] {
                let(c,inputs,out)=build(&g,mode)?;
                for bits in 0..4 {
                    let input=[(bits&1) as u8,((bits>>1)&1) as u8];
                    let expected=if right==u64::MAX{input[0]^input[1]}else{input[0]&input[1]};
                    assert_eq!(evaluate(&g,&input)?,expected as u64);
                    fill(&c,&inputs,out,&input,expected as u64)?;
                    assert!(fill(&c,&inputs,out,&input,(expected^1) as u64).is_err());
                }
            }
        }Ok(())
    }
    #[test]
    fn same_boolean_relation_both_frontends() -> Result<()> {
        for mode in ["native-default", "preserved-graph"] {
            for right in [u64::MAX, 0] {
                let g = Graph { format:"general-binary-feedback-v1".into(),task:"xor_and_random".into(), inputs:3,gates:vec![Gate{left:vec![0,1,2],right}] };
                let (c, inputs, out) = build(&g, mode)?;
                for bits in 0..8 { let input = [(bits&1) as u8,((bits>>1)&1) as u8,((bits>>2)&1) as u8];
                    let value = evaluate(&g,&input)?;
                    fill(&c,&inputs,out,&input,value)?;
                    assert!(fill(&c,&inputs,out,&input,value^1).is_err());
                }
                assert!(fill(&c,&inputs,out,&[2,0,0],0).is_err());
            }
        } Ok(())
    }
}
