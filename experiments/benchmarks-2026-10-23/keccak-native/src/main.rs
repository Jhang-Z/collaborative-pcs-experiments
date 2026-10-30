//! One native Binius64 ZK proof for an ordered batch of private200-byte Keccak-f states, public first256outputbits.
use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    time::Instant,
};

use anyhow::{Context, Result, ensure};
use binius_circuits::keccak::{keccak_f1600,ref_keccak_f1600};
use binius_core::{constraint_system::ValueVec, word::Word};
use binius_frontend::{Circuit, CircuitBuilder, Wire};
use binius_hash::sha256::Sha256HashSuite;
use binius_prover::{OptimalPackedB128, zk_config::ZKProver};
use binius_utils::{DeserializeBytes, SerializeBytes};
use binius_verifier::{
    SECURITY_BITS,
    config::StdChallenger,
    transcript::{ProverTranscript, VerifierTranscript},
    zk_config::ZKVerifier,
};
use clap::{Parser, Subcommand};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const COMMIT: &str = "4428e759dd27956bd5b9ae5025d67eb8ccc1accf";
const LOG_INV_RATE: usize = 1; // Upstream example CLI default, preserved without tuning.
type Prover = ZKProver<OptimalPackedB128, Sha256HashSuite>;
type Verifier = ZKVerifier<Sha256HashSuite>;

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Cache only public circuit-dependent setup; no input file or witness is accepted.
    Prepare {
        #[arg(long)]
        messages: usize,
        #[arg(long)]
        out: PathBuf,
    },
    /// Fresh witness and cache restoration precede the measured native ZK proof.
    Prove {
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        messages: usize,
        #[arg(long)]
        prepared: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    /// Independent verification reads public digests and proof, never private input.
    Verify {
        #[arg(long)]
        messages: usize,
        #[arg(long)]
        prepared: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
}

struct BatchCircuit {
    circuit: Circuit,
    inputs: Vec<[Wire; 25]>,
    outputs: Vec<[Wire; 4]>,
}

fn build(messages: usize) -> Result<BatchCircuit> {
    ensure!(
        [2, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096].contains(&messages),
        "unsupported message count"
    );
    let builder = CircuitBuilder::new();
    let mut inputs = Vec::with_capacity(messages);
    let mut outputs = Vec::with_capacity(messages);
    for i in 0..messages {
        let b=builder.subcircuit(format!("keccak_f1600[{i}]"));
        let input:[Wire;25]=std::array::from_fn(|_|b.add_witness());
        let mut computed=input;keccak_f1600(&b,&mut computed);
        let output:[Wire;4]=std::array::from_fn(|_|b.add_inout());
        b.assert_eq_v("public_first256", std::array::from_fn::<_,4,_>(|i|computed[i]), output);
        inputs.push(input);
        outputs.push(output);
    }
    let circuit = builder.build();
    let ordered: Vec<_> = outputs.iter().flatten().copied().collect();
    ensure!(circuit.inout() == ordered, "unexpected public-input order");
    ensure!(
        circuit.constraint_system().n_inout == messages * 4,
        "private input escaped into public interface"
    );
    Ok(BatchCircuit {
        circuit,
        inputs,
        outputs,
    })
}

fn words(bytes: &[u8]) -> Vec<Word> {
    bytes
        .chunks_exact(8)
        .map(|c| Word(u64::from_le_bytes(c.try_into().unwrap())))
        .collect()
}

fn output(input:&[u8])->Vec<u8> {
 input.chunks_exact(200).flat_map(|b| {
  let mut state:[u64;25]=std::array::from_fn(|i|u64::from_le_bytes(b[i*8..i*8+8].try_into().unwrap()));
  ref_keccak_f1600(&mut state);state[..4].iter().flat_map(|v|v.to_le_bytes()).collect::<Vec<_>>()
 }).collect()
}
fn fill(batch: &BatchCircuit, input: &[u8], digests: &[u8]) -> Result<ValueVec> {
    ensure!(input.len()==batch.inputs.len()*200 && digests.len()==batch.outputs.len()*32,"state/output byte counts");
    let mut w = batch.circuit.new_witness_filler();
    for (&wire, value) in batch.inputs.iter().flatten().zip(words(input)) {
        w[wire] = value;
    }
    for (&wire, value) in batch.outputs.iter().flatten().zip(words(digests)) {
        w[wire] = value;
    }
    batch.circuit.populate_wire_witness(&mut w)?;
    let w = w.into_value_vec();
    batch.circuit.constraint_system().verify(&w)?;
    ensure!(
        w.inout() == words(digests),
        "public inputs differ from ordered digests"
    );
    Ok(w)
}

fn serialize(value: &impl SerializeBytes) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    value.serialize(&mut bytes)?;
    Ok(bytes)
}
fn deserialize<T: DeserializeBytes>(bytes: &[u8]) -> Result<T> {
    let mut remaining = bytes;
    let value = T::deserialize(&mut remaining)?;
    ensure!(remaining.is_empty(), "trailing bytes in cached artifact");
    Ok(value)
}
fn hash(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}
fn ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}
fn emit(value: &Value) -> Result<()> {
    println!("{value}");
    io::stdout().flush()?;
    Ok(())
}
fn save_json(dir: &Path, name: &str, value: &Value) -> Result<()> {
    fs::write(dir.join(name), serde_json::to_vec_pretty(value)?)?;
    Ok(())
}
fn read_json(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}
fn threads() -> Result<()> {
    ensure!(
        std::env::var("RAYON_NUM_THREADS").as_deref() == Ok("1"),
        "set RAYON_NUM_THREADS=1; pin the process externally for single-core measurements"
    );
    ensure!(
        binius_utils::rayon::current_num_threads() == 1,
        "Binius64 worker count is not one"
    );
    Ok(())
}

fn parameters(verifier: &Verifier) -> Value {
    let fri = verifier.basefold_compiler().fri_params();
    let blind = verifier
        .outer_iop_verifier()
        .constraint_system()
        .blinding_info();
    let cs = verifier.constraint_system();
    json!({"upstream_commit": COMMIT, "native_security_bits_parameter": SECURITY_BITS,
        "security_parameter_scope": "FRI query phase only; not an asserted total security level",
        "field": "Ghash128b", "field_bits": 128, "hash_suite": "Sha256HashSuite",
        "fiat_shamir": "HasherChallenger<Sha256>", "hash_digest_bits": 256,
        "log_inv_rate": verifier.log_inv_rate(), "rs_rate": 0.5,
        "fri_queries": fri.n_test_queries(), "fri_fold_arities": fri.fold_arities(),
        "fri_rs_log_dim": fri.rs_code().log_dim(), "fri_rs_log_len": fri.rs_code().log_len(),
        "outer_dummy_wires_per_segment": blind.n_dummy_wires,
        "outer_dummy_constraints_per_segment": blind.n_dummy_constraints,
        "public_words": cs.n_inout, "private_words": cs.n_private,
        "and_constraints": cs.and_constraints.len(), "zero_constraints": cs.zero_constraints.len(),
        "imul_constraints": cs.imul_constraints.len(), "bmul_constraints": cs.bmul_constraints.len(),
        "rayon_threads": binius_utils::rayon::current_num_threads()})
}

fn prepare(messages: usize, out: &Path) -> Result<()> {
    fs::create_dir_all(out)?;
    ensure!(
        !out.join("cache.json").exists(),
        "cache already exists; choose a new directory"
    );
    emit(&json!({"event":"prepare_start", "messages":messages}))?;
    let start = Instant::now();
    let batch = build(messages)?;
    let circuit_ms = ms(start);
    let setup = Instant::now();
    let verifier = Verifier::setup(batch.circuit.constraint_system().clone(), LOG_INV_RATE)?;
    let prover = Prover::setup(&verifier)?;
    let setup_ms = ms(setup);
    let encoding = Instant::now();
    let prover_bytes = serialize(&prover)?;
    let verifier_bytes = serialize(&verifier)?;
    let cs_hash = hash(&serialize(batch.circuit.constraint_system())?);
    let cache_serialize_ms = ms(encoding);
    let prepare_compute_ms = ms(start);
    let manifest = json!({"schema":"binius64-keccak-f1600-truncated256-zk-v1", "event":"prepare_complete",
        "messages":messages, "message_bytes":200, "proof_count":1, "zero_knowledge":true,
        "upstream_commit":COMMIT, "constraint_system_sha256":cs_hash,
        "prover_cache_sha256":hash(&prover_bytes), "verifier_cache_sha256":hash(&verifier_bytes),
        "circuit_ms":circuit_ms, "public_setup_ms":setup_ms, "cache_serialize_ms":cache_serialize_ms,
        "prepare_compute_ms":prepare_compute_ms, "parameters":parameters(&verifier),
        "contains_witness":false, "contains_proof_randomness":false});
    fs::write(out.join("prover.bin"), prover_bytes)?;
    fs::write(out.join("verifier.bin"), verifier_bytes)?;
    save_json(out, "cache.json", &manifest)?;
    emit(&manifest)
}

fn checked_cache(prepared: &Path, messages: usize, batch: &BatchCircuit) -> Result<Value> {
    let manifest = read_json(&prepared.join("cache.json"))?;
    ensure!(
        manifest["upstream_commit"] == COMMIT && manifest["messages"] == messages,
        "cache version or message count mismatch"
    );
    ensure!(
        manifest["constraint_system_sha256"]
            == hash(&serialize(batch.circuit.constraint_system())?),
        "cache is not the canonical private-message/public-digest circuit"
    );
    Ok(manifest)
}

fn prove(input_path: &Path, messages: usize, prepared: &Path, out: &Path) -> Result<()> {
    fs::create_dir_all(out)?;
    ensure!(
        !out.join("proof.bin").exists(),
        "proof already exists; use a fresh trial directory"
    );
    emit(&json!({"event":"prepare_start", "messages":messages}))?;
    let preparation = Instant::now();
    let all_input = fs::read(input_path).context("read private Keccak states")?;
    ensure!(
        all_input.len() >= messages * 200,
        "master input must contain enough consecutive200-byte Keccak states"
    );
    let circuit_start = Instant::now();
    let batch = build(messages)?;
    let circuit_ms = ms(circuit_start);
    let manifest = checked_cache(prepared, messages, &batch)?;
    let prover_bytes = fs::read(prepared.join("prover.bin"))?;
    ensure!(
        manifest["prover_cache_sha256"] == hash(&prover_bytes),
        "prover cache hash mismatch"
    );
    let restore = Instant::now();
    let prover: Prover = deserialize(&prover_bytes)?;
    let cache_restore_ms = ms(restore);
    ensure!(
        hash(&serialize(prover.inner_iop_prover().constraint_system())?)
            == manifest["constraint_system_sha256"],
        "prover cache has an unexpected circuit"
    );
    let witness_start = Instant::now();
    let input = &all_input[..messages * 200];
    let digests: Vec<u8> = output(input);
    let witness = fill(&batch, input, &digests)?;
    let witness_ms = ms(witness_start);
    let input_sha256 = hash(input);
    let master_sha256 = hash(&all_input);
    drop(batch);
    drop(prover_bytes);
    let prepare_wall_ms = ms(preparation);
    emit(
        &json!({"event":"online_start", "messages":messages, "prepare_wall_ms":prepare_wall_ms,
        "circuit_ms":circuit_ms, "cache_restore_ms":cache_restore_ms, "witness_ms":witness_ms}),
    )?;
    // This is the entire upstream create_proof_zk path, including RNG, commit, inner proof,
    // wrapper witness/proof, and transcript serialization. No I/O is inside this interval.
    let online = Instant::now();
    let mut transcript = ProverTranscript::new(StdChallenger::default());
    let mut rng = rand::rng();
    prover.prove(&witness, &mut rng, &mut transcript)?;
    let proof = transcript.finalize();
    let online_ms = ms(online);
    emit(&json!({"event":"online_complete", "online_ms":online_ms, "proof_bytes":proof.len()}))?;
    let result = json!({"schema":"binius64-keccak-f1600-truncated256-zk-v1", "event":"prove_complete",
        "upstream_commit":COMMIT, "messages":messages, "message_bytes":200,
        "input_prefix_sha256":input_sha256, "input_master_sha256":master_sha256,
        "ordered_digests_sha256":hash(&digests), "proof_sha256":hash(&proof), "proof_count":1,
        "proof_bytes":proof.len(), "zero_knowledge":true, "verification":null,
        "prepare_wall_ms":prepare_wall_ms, "circuit_ms":circuit_ms,
        "cache_restore_ms":cache_restore_ms, "witness_ms":witness_ms, "online_ms":online_ms,
        "parameters":manifest["parameters"],
        "proof_randomness":"fresh native rand::rng inside online; no random material reused",
        "online_includes":["native RNG", "commitments", "inner IOP", "ZK wrapper witness and proof", "transcript finalization/serialization"],
        "online_excludes":["public circuit/setup/cache restoration", "Keccak input witness", "file I/O", "verification"]});
    fs::write(out.join("proof.bin"), proof)?;
    fs::write(out.join("digests.bin"), digests)?;
    save_json(out, "prove.json", &result)?;
    emit(&result)
}

fn verify(messages: usize, prepared: &Path, out: &Path) -> Result<()> {
    emit(&json!({"event":"verify_prepare_start", "messages":messages}))?;
    let prep = Instant::now();
    let batch = build(messages)?;
    let manifest = checked_cache(prepared, messages, &batch)?;
    let verifier_bytes = fs::read(prepared.join("verifier.bin"))?;
    ensure!(
        manifest["verifier_cache_sha256"] == hash(&verifier_bytes),
        "verifier cache hash mismatch"
    );
    let verifier: Verifier = deserialize(&verifier_bytes)?;
    ensure!(
        hash(&serialize(verifier.constraint_system())?) == manifest["constraint_system_sha256"],
        "verifier cache has an unexpected circuit"
    );
    let digests = fs::read(out.join("digests.bin"))?;
    ensure!(digests.len() == messages * 32, "wrong public digest count");
    let public_words = words(&digests);
    let proof = fs::read(out.join("proof.bin"))?;
    let proof_size = proof.len();
    drop(batch);
    let prepare_ms = ms(prep);
    emit(&json!({"event":"verify_start", "messages":messages, "prepare_ms":prepare_ms}))?;
    let start = Instant::now();
    let mut transcript = VerifierTranscript::new(StdChallenger::default(), proof);
    let verification = verifier
        .verify(&public_words, &mut transcript)
        .map_err(anyhow::Error::from)
        .and_then(|_| transcript.finalize().map_err(anyhow::Error::from));
    let verify_ms = ms(start);
    let result = json!({"schema":"binius64-keccak-f1600-truncated256-zk-v1", "event":"verify_complete",
        "messages":messages, "proof_count":1, "proof_bytes":proof_size, "verification":verification.is_ok(),
        "verify_ms":verify_ms, "verify_prepare_ms":prepare_ms, "parameters":parameters(&verifier),
        "error":verification.as_ref().err().map(|e| format!("{e:#}"))});
    save_json(out, "verify.json", &result)?;
    emit(&result)?;
    verification
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    threads()?;
    match cli.command {
        Command::Prepare { messages, out } => prepare(messages, &out),
        Command::Prove {
            input,
            messages,
            prepared,
            out,
        } => prove(&input, messages, &prepared, &out),
        Command::Verify {
            messages,
            prepared,
            out,
        } => verify(messages, &prepared, &out),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn private_states_public_truncated_outputs_and_negative_witness() {
        let batch = build(8).unwrap();
        let input: Vec<u8> = (0..1600).map(|i| i as u8).collect();
        let mut digests: Vec<u8> = output(&input);
        fill(&batch, &input, &digests).unwrap();
        digests[0] ^= 1;
        assert!(fill(&batch, &input, &digests).is_err());
    }
}
