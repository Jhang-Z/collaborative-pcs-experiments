//! Independent TCP roles for the standalone PCS online experiment.
use anyhow::{Context, Result, ensure};
use b2proto::{
    field::{D, LOG_D},
    net,
    params::{Layout, Params, ell_for_bits},
    pcs_codec, protocol,
    setup::{Setup, instance_point},
};
use binius_hash::Blake3HashSuite;
use clap::{Args, Parser, Subcommand};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{self, Write},
    net::TcpListener,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}
#[derive(Args, Clone)]
struct Shape {
    #[arg(long)]
    parties: usize,
    #[arg(long)]
    log_bits: usize,
    /// Public evaluation-point seed only. Never used for shares, masks, padding, or salts.
    #[arg(long, default_value_t = 20261023)]
    point_seed: u64,
    #[arg(long, default_value_t = 871)]
    gamma: usize,
    #[arg(long, default_value_t = 4)]
    tau: usize,
    #[arg(long)]
    development: bool,
}
#[derive(Subcommand)]
enum Command {
    Describe {
        #[command(flatten)]
        shape: Shape,
    },
    Aggregator {
        #[command(flatten)]
        shape: Shape,
        #[arg(long)]
        listen: String,
        #[arg(long)]
        out: PathBuf,
    },
    Party {
        #[command(flatten)]
        shape: Shape,
        #[arg(long)]
        id: usize,
        #[arg(long)]
        connect: String,
    },
    Client {
        #[command(flatten)]
        shape: Shape,
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        connect: String,
    },
    Verify {
        #[arg(long)]
        out: PathBuf,
    },
    Simulate {
        #[command(flatten)]
        shape: Shape,
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        trace: PathBuf,
    },
}
fn emit(v: &Value) {
    println!("{v}");
    io::stdout().flush().expect("flush JSON event");
}
fn save(out: &Path, name: &str, v: &Value) -> Result<()> {
    fs::write(out.join(name), serde_json::to_vec_pretty(v)?)?;
    Ok(())
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn hash(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn ms(t: Duration) -> f64 {
    t.as_secs_f64() * 1000.0
}
fn params(s: &Shape) -> Result<Params> {
    ensure!(
        s.parties >= 4 && s.parties.is_power_of_two(),
        "N must be a power of two >= 4"
    );
    ensure!(
        s.log_bits >= LOG_D && s.log_bits < usize::BITS as usize,
        "input size must fit the address space and contain a full packing block"
    );
    ensure!(
        s.development || (s.gamma == 871 && s.tau == 4),
        "non-plan parameters require --development"
    );
    ensure!(
        s.gamma >= 4 && s.gamma.checked_add(2).is_some()
            && s.tau >= 3
            && s.tau < b2proto::params::ceil_log2(s.gamma + 2),
        "unsupported query/tail parameters"
    );
    let p = Params {
        n_parties: s.parties,
        ell: ell_for_bits(s.parties, s.gamma, s.tau, 2, 1usize << s.log_bits),
        beta: 2,
        gamma: s.gamma,
        tau: s.tau,
        salt_bytes: 32,
    };
    p.validate();
    Ok(p)
}
fn description(s: &Shape, p: &Params) -> Value {
    let layout = Layout::verifier(p);
    let data_entries = layout.n_data_entries();
    json!({
    "scheme":"ours-standalone-pcs", "messages":"one commitment and one evaluation opening", "M_bits":1usize<<s.log_bits,
    "log_bits":s.log_bits,"N":s.parties,"k":p.k(),"k_prime":p.kp(),"privacy_threshold":p.kp()-p.k(),
    "ell":p.ell,"field_bits":D,"d":D,"beta":p.beta,"row_code_rate":"1/4","gamma":s.gamma,"tau":s.tau,
    "hash":"BLAKE3","hash_bits":256,"salt_bits":256,"point_seed":s.point_seed,"development":s.development,
    "standalone_soundness_target_bits":if s.development{None}else{Some(100)},"analysis_q_H":"2^64","target_applies_to_development_parameters":false,
    "q_A":"not identified with q_H; no concrete privacy error claim here",
    "input_mapping":"file bytes in order; LSB first within each byte; groups of 256 bits packed in GhashSq256b basis; data slots in owner/column/logical-row order; unused data slots zero",
    "evaluation_domain":"native padded multilinear domain excluding mask and padding coordinates from data claim",
    "packed_input_elements":(1usize<<s.log_bits)/D,"native_logical_table_cells":p.k()*p.n(),
    "native_padding_columns":layout.pad.len(),"native_tensor_mask_cells":layout.masks.iter().map(Vec::len).sum::<usize>(),
    "native_data_capacity_bits":data_entries*D,"native_row_codeword_elements":1usize<<p.m(),
    "point_dimensions":[LOG_D,p.k().ilog2() as usize,p.ell],"proof_format":std::str::from_utf8(pcs_codec::PROOF_MAGIC).expect("ASCII proof format"),
    "execution_model":"N independent party processes; trusted ideal F_Agg/F_rand aggregator relays input shares",
    "cpu_network_binding":"external launcher; aggregator must share node 0 CPU/network budget",
    "proof_randomness":"fresh OS entropy per client, padding dealer, and party; all salts prepared before ready"})
}
fn event(role: &str, name: &str) {
    emit(&json!({"role":role,"event":name}));
}

fn aggregator(s: Shape, listen: &str, out: &Path) -> Result<()> {
    ensure!(!out.exists(), "choose a fresh output directory");
    fs::create_dir_all(out)?;
    event("aggregator", "prepare_start");
    let prep = Instant::now();
    let p = params(&s)?;
    let desc = description(&s, &p);
    let setup = Setup::new(p);
    let public_setup_ms = ms(prep.elapsed());
    let listener = TcpListener::bind(listen)?;
    emit(&json!({"role":"aggregator","event":"listen_ready","address":listen,"parameters":desc}));
    let mut prepare_ms = None;
    let artifact = net::run_aggregator_external::<Blake3HashSuite>(
        &setup,
        s.point_seed,
        1 << s.log_bits,
        listener,
        &mut |e| {
            if e == "online_start" {
                prepare_ms = Some(ms(prep.elapsed()));
            }
            event("aggregator", e)
        },
    );
    let r = &artifact.report;
    let instance = artifact.instance.to_bytes();
    let statement = json!({"schema":"ours-pcs-statement-v1","parameters":desc,"input_prefix_sha256":hex(&artifact.input_prefix_hash),"commitment_hex":hex(&artifact.commitment),
        "instance_sha256":hash(&instance),"point_bytes_hex":hex(&instance[..instance.len()-32]),"claim_hex":hex(&instance[instance.len()-32..])});
    let result = json!({"schema":"ours-pcs-online-v1","event":"prove_complete","role":"aggregator","parameters":desc,
        "public_setup_ms":public_setup_ms,"prepare_ms":prepare_ms.expect("online start event"),
        "client_share_ms":ms(r.client_share),"client_sent_bytes_with_framing":r.client_sent,
        "online_ms":ms(r.online),"serialization_ms":ms(r.serialization),"online_payload_bytes":r.online_bytes,
        "party_online_payload_up_down":r.online_party_payload,"party_compute_us":r.party_compute_us,
        "proof_count":1,"proof_bytes":artifact.proof.len(),"proof_sha256":hash(&artifact.proof),
        "input_prefix_sha256":hex(&artifact.input_prefix_hash),"instance_sha256":hash(&instance),"commitment_hex":hex(&artifact.commitment),
        "internal_verification":false,"verification":null,"online_excludes_disk_and_verification":true,
        "online_start_boundary":"all parties acknowledged fresh complete shares and salts; before go and witness encoding",
        "online_stop_boundary":"complete canonical proof bytes available at aggregator",
        "online_payload_accounting":"each aggregator-party send counted once; excludes 8-byte frame headers, preparation, diagnostics and proof writes"});
    // run_aggregator_external emits/flushed online_complete before returning or these writes.
    fs::write(out.join("instance.bin"), instance)?;
    fs::write(out.join("proof.bin"), artifact.proof)?;
    save(out, "statement.json", &statement)?;
    save(out, "prove.json", &result)?;
    emit(&result);
    Ok(())
}
fn party(s: Shape, id: usize, connect: &str) -> Result<()> {
    ensure!(id < s.parties, "party ID out of range");
    event("party", "prepare_start");
    let start = Instant::now();
    let setup = Setup::new(params(&s)?);
    net::run_party_external::<Blake3HashSuite>(
        &setup,
        id,
        s.point_seed,
        1 << s.log_bits,
        connect,
        &mut |e| emit(&json!({"role":"party","id":id,"event":e})),
    );
    emit(
        &json!({"role":"party","id":id,"event":"party_complete","role_wall_ms":ms(start.elapsed())}),
    );
    Ok(())
}
fn client(s: Shape, input: &Path, connect: &str) -> Result<()> {
    event("client", "prepare_start");
    let start = Instant::now();
    let setup = Setup::new(params(&s)?);
    let master = fs::read(input)?;
    ensure!(
        master.len() >= (1usize << s.log_bits) / 8,
        "input is shorter than the requested bit table"
    );
    let prefix = &master[..(1 << s.log_bits) / 8];
    let master_hash = hash(&master);
    let prefix_hash = hash(prefix);
    net::run_client_external(
        &setup,
        s.point_seed,
        prefix,
        connect,
        &mut |sharing, sent| {
            emit(
                &json!({"role":"client","event":"client_ready","prepare_ms":ms(start.elapsed()),"share_ms":ms(sharing),"sent_bytes_with_framing_before_ready":sent,
        "input_master_sha256":master_hash,"input_prefix_sha256":prefix_hash,"M_bits":1usize<<s.log_bits}),
            )
        },
    );
    event("client", "client_complete");
    Ok(())
}
fn simulate(s: Shape, input: &Path, out: &Path, trace_path: &Path) -> Result<()> {
    ensure!(!out.exists(), "choose a fresh output directory");
    let setup_start = Instant::now();
    let setup = Setup::new(params(&s)?);
    let mut desc = description(&s, &setup.params);
    desc["execution_model"] = json!("sequential real party computation with virtual LAN replay; host holds all private states");
    let public_setup_ms = ms(setup_start.elapsed());
    let master = fs::read(input)?;
    ensure!(master.len() >= (1usize << s.log_bits) / 8, "input is shorter than the requested bit table");
    let (artifact, trace) = b2proto::net_simulation::simulate_external::<Blake3HashSuite>(
        &setup, s.point_seed, &master[..(1 << s.log_bits)/8]);
    let instance = artifact.instance.to_bytes();
    let r = &artifact.report;
    fs::create_dir_all(out)?;
    fs::write(out.join("instance.bin"), &instance)?;
    fs::write(out.join("proof.bin"), &artifact.proof)?;
    save(out, "statement.json", &json!({"schema":"ours-pcs-statement-v1","parameters":desc,
        "input_prefix_sha256":hex(&artifact.input_prefix_hash),"commitment_hex":hex(&artifact.commitment),
        "instance_sha256":hash(&instance),"point_bytes_hex":hex(&instance[..instance.len()-32]),
        "claim_hex":hex(&instance[instance.len()-32..])}))?;
    let exchanges: Vec<_> = trace.exchanges.iter().map(|e| json!({"command":e.command,
        "coordinator_ns":e.coordinator_ns,"party_ns":e.party_ns,
        "request_bytes":e.request_bytes,"response_bytes":e.response_bytes})).collect();
    fs::write(trace_path, serde_json::to_vec_pretty(&json!({"schema":"full-sha-sequential-exchanges-v1",
        "task":"standalone-pcs","parties":s.parties,"exchanges":exchanges,
        "coordinator_final_ns":trace.coordinator_final_ns,"private_payloads_recorded":false,
        "measurement":"sequential real kernels matching external PCS TCP message schedule"}))?)?;
    let result = json!({"schema":"ours-pcs-online-v1","event":"prove_complete","parameters":desc,
        "public_setup_ms":public_setup_ms,"prepare_ms":ms(r.preparation),"client_share_ms":ms(r.client_share),
        "online_ms":ms(r.online),"online_ms_kind":"sequential harness wall time; use trace replay for virtual latency",
        "serialization_ms":ms(r.serialization),"online_payload_bytes":r.online_bytes,
        "online_framing_bytes":trace.exchanges.len()*s.parties*16,"online_exchange_rounds":trace.exchanges.len(),
        "party_online_payload_up_down":r.online_party_payload,"proof_count":1,"proof_bytes":artifact.proof.len(),
        "proof_sha256":hash(&artifact.proof),"input_prefix_sha256":hex(&artifact.input_prefix_hash),
        "instance_sha256":hash(&instance),"commitment_hex":hex(&artifact.commitment),
        "private_material_fresh_os_entropy":true,"simulation_host_holds_all_private_states":true,
        "internal_verification":false,"verification":null,"online_excludes_disk_and_verification":true,
        "online_start_boundary":"fresh shares and salts prepared; before go and witness encoding",
        "online_stop_boundary":"complete canonical proof bytes available at aggregator"});
    save(out,"prove.json",&result)?;
    emit(&result);
    Ok(())
}
fn number(v: &Value, k: &str) -> Result<usize> {
    usize::try_from(v[k].as_u64().with_context(|| format!("missing {k}"))?).context("integer range")
}
fn verify(out: &Path) -> Result<()> {
    event("verifier", "verify_prepare_start");
    let preparation = Instant::now();
    let statement: Value = serde_json::from_slice(&fs::read(out.join("statement.json"))?)?;
    let p = &statement["parameters"];
    let s = Shape {
        parties: number(p, "N")?,
        log_bits: number(p, "log_bits")?,
        point_seed: p["point_seed"].as_u64().context("point seed")?,
        gamma: number(p, "gamma")?,
        tau: number(p, "tau")?,
        development: p["development"].as_bool().context("development flag")?,
    };
    let setup = Setup::verifier(params(&s)?);
    let instance_bytes = fs::read(out.join("instance.bin"))?;
    let proof_bytes = fs::read(out.join("proof.bin"))?;
    let verify_prepare_ms = ms(preparation.elapsed());
    event("verifier", "verify_start");
    let start = Instant::now();
    let verified = (|| -> Result<()> {
        let inst =
            pcs_codec::decode_instance(&setup, &instance_bytes).map_err(anyhow::Error::msg)?;
        let point = instance_point(&setup, s.point_seed);
        ensure!(
            inst.r_h == point.0 && inst.r_a == point.1 && inst.r_b == point.2,
            "fixed public point mismatch"
        );
        ensure!(
            statement["instance_sha256"].as_str() == Some(hash(&instance_bytes).as_str()),
            "instance metadata mismatch"
        );
        ensure!(
            statement["point_bytes_hex"].as_str()
                == Some(hex(&instance_bytes[..instance_bytes.len() - 32]).as_str())
                && statement["claim_hex"].as_str()
                    == Some(hex(&instance_bytes[instance_bytes.len() - 32..]).as_str()),
            "public point/claim metadata mismatch"
        );
        let proof = pcs_codec::decode_proof(&setup, &proof_bytes).map_err(anyhow::Error::msg)?;
        ensure!(
            statement["commitment_hex"].as_str() == Some(hex(&proof.roots[0]).as_str()),
            "external commitment mismatch"
        );
        protocol::verify::<Blake3HashSuite>(&setup, &inst, &proof).map_err(anyhow::Error::msg)?;
        Ok(())
    })();
    let result = json!({"role":"verifier","event":"verify_complete","verification":verified.is_ok(),"verify_ms":ms(start.elapsed()),"verify_prepare_ms":verify_prepare_ms,
        "proof_decode_included":true,"proof_count":1,"proof_bytes":proof_bytes.len(),"private_input_loaded":false,"independent_process":true,
        "error":verified.as_ref().err().map(|e|format!("{e:#}"))});
    save(out, "verify.json", &result)?;
    emit(&result);
    verified
}
fn main() -> Result<()> {
    ensure!(
        std::env::var("RAYON_NUM_THREADS").as_deref() == Ok("1"),
        "set RAYON_NUM_THREADS=1 for every role"
    );
    match Cli::parse().command {
        Command::Describe { shape } => {
            emit(&description(&shape, &params(&shape)?));
            Ok(())
        }
        Command::Aggregator { shape, listen, out } => aggregator(shape, &listen, &out),
        Command::Party { shape, id, connect } => party(shape, id, &connect),
        Command::Client {
            shape,
            input,
            connect,
        } => client(shape, &input, &connect),
        Command::Verify { out } => verify(&out),
        Command::Simulate { shape, input, out, trace } => simulate(shape, &input, &out, &trace),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(parties: usize, log_bits: usize) -> Shape {
        Shape { parties, log_bits, point_seed: 20261023, gamma: 871, tau: 4, development: false }
    }

    #[test]
    fn worker_count_and_table_length_are_runtime_parameters() {
        for n in [32, 64, 128, 256, 512] {
            for log_bits in [16, 17, 18, 20, 22, 24] {
                let s = shape(n, log_bits);
                let p = params(&s).expect("valid protocol dimensions");
                assert_eq!(p.n_parties, n);
                let layout = b2proto::params::Layout::verifier(&p);
                assert!(b2proto::params::input_bits(&layout) >= 1usize << log_bits);
            }
        }
    }

    #[test]
    fn description_uses_the_global_mask_count_and_current_proof_format() {
        let s = shape(32, 16);
        let d = description(&s, &params(&s).unwrap());
        assert_eq!(d["native_tensor_mask_cells"], 256);
        assert_eq!(d["native_data_capacity_bits"], 243712);
        assert_eq!(d["proof_format"], "B2PCS004");
    }

    #[test]
    fn invalid_dimensions_are_rejected_before_layout_construction() {
        for n in [0, 1, 2, 3, 31, 96] { assert!(params(&shape(n, 16)).is_err()); }
        for log_bits in [0, 7, usize::BITS as usize] {
            assert!(params(&shape(32, log_bits)).is_err());
        }
    }
}
