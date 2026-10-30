//! Public coordinator with indexed and fixed-SHA structured matrix verification.
//! No party share files are opened.
use crate::{
    field::{D, Field, L},
    fs::Transcript,
    indexed::{self, Index, MatrixProof},
    merkle::{Hash, Hasher, Tree},
    prepare::Shape,
    protocol::{self, Opening, Proof},
    setup::{Instance, Setup},
    sha_spartan::sparse_fold,
    preprocessing::{PublicPreprocessing,context_cache_payload_bytes,fixed_interpolation_payload_bytes},
    sha_zk,
    application::StructuredKey,
    spartan::{eq_eval, interp},
    wire::{self, Reader, *},
    zk,
};
use anyhow::{Result, ensure};
use binius_hash::Blake3HashSuite as H;
use std::{
    fs,
    io::Write,
    net::{TcpListener, TcpStream},
    path::Path,
    time::Instant,
    sync::Arc,
};
const ZERO: Hash = [0; 32];
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub enum MatrixMode {
    Indexed,
    Structured,
}
impl MatrixMode {
    fn name(self) -> &'static str {
        match self { Self::Indexed => "indexed", Self::Structured => "structured" }
    }
}
fn bytes(v: &[L]) -> &[u8] {
    bytemuck::cast_slice(v)
}
struct Bus {
    peers: Vec<TcpStream>,
    simulation: Option<crate::simulation::Simulation>,
    sent: u64,
    received: u64,
    frames: u64,
    rounds: u64,
}
impl Bus {
    fn accept(address: &str, n: usize) -> Result<Self> {
        let listener = TcpListener::bind(address)?;
        println!(
            "{}",
            serde_json::json!({"event":"listening","address":listener.local_addr()?.to_string()})
        );
        std::io::stdout().flush()?;
        let mut peers: Vec<Option<TcpStream>> = (0..n).map(|_| None).collect();
        for _ in 0..n {
            let (mut s, _) = listener.accept()?;
            s.set_nodelay(true)?;
            let b = wire::receive(&mut s)?;
            let mut r = Reader(&b);
            ensure!(r.take(8)? == b"FSREADY1", "ready magic");
            let id = r.u64()? as usize;
            r.finish()?;
            ensure!(
                id < n && peers[id].is_none(),
                "duplicate/invalid party identity"
            );
            peers[id] = Some(s);
        }
        Ok(Self {
            peers: peers.into_iter().map(Option::unwrap).collect(),
            simulation: None,
            sent: 0,
            received: 0,
            frames: 0,
            rounds: 0,
        })
    }
    fn exchange(&mut self, req: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>> {
        if let Some(sim) = &mut self.simulation {
            let out = sim.exchange(&req)?;
            self.sent += req.iter().map(|b| b.len() as u64).sum::<u64>();
            self.received += out.iter().map(|b| b.len() as u64).sum::<u64>();
            self.frames += 16 * req.len() as u64;
            self.rounds += 1;
            return Ok(out);
        }
        ensure!(req.len() == self.peers.len(), "request count");
        for (s, b) in self.peers.iter_mut().zip(&req) {
            wire::send(s, b)?;
            self.sent += b.len() as u64;
            self.frames += 8;
        }
        let mut out = vec![];
        for s in &mut self.peers {
            let b = wire::receive(s)?;
            self.received += b.len() as u64;
            self.frames += 8;
            out.push(b);
        }
        self.rounds += 1;
        Ok(out)
    }
    fn all(&mut self, b: Vec<u8>) -> Result<Vec<Vec<u8>>> {
        let n = self.simulation.as_ref().map_or(self.peers.len(), |s| s.parties());
        self.exchange(vec![b; n])
    }
    fn empty(&mut self, tag: u8, x: &[L]) -> Result<()> {
        let a = self.all(wire::command(tag, x))?;
        ensure!(
            a.iter().all(Vec::is_empty),
            "unexpected acknowledgement payload"
        );
        Ok(())
    }
    fn sum(&mut self, b: Vec<u8>, n: usize) -> Result<Vec<L>> {
        let mut sum = vec![L::ZERO; n];
        for v in self.all(b)? {
            for (a, x) in sum.iter_mut().zip(wire::scalars(&v, n)?) {
                *a += x;
            }
        }
        Ok(sum)
    }
}
fn collect_hashes(v: Vec<Vec<u8>>) -> Result<Vec<Hash>> {
    v.into_iter()
        .map(|b| {
            ensure!(b.len() == 32, "root response length");
            Ok(b.try_into().unwrap())
        })
        .collect()
}

fn open(
    bus: &mut Bus,
    setup: &Setup,
    root_leaves: Vec<Hash>,
    tr: &mut Transcript<'_, H>,
    functional: Option<(&[usize], &[L])>,
    instance: Option<&Instance>,
) -> Result<Proof> {
    let is_g = functional.is_some();
    let role = if is_g { zk::G_ROLE } else { zk::BIT_ROLE };
    let h = Hasher::<H>::scoped(role);
    let mut tops = vec![Tree::build(&h.at_layer(0), root_leaves)];
    let mut roots = vec![tops[0].root()];
    let dummy = protocol::dummy_root(&h,4);
    let (xi, t, h_omega, eps, r_pp) = if let Some((_map, weights)) = functional {
        let mut c = tr.round(&roots[0], b"v04 G functional");
        let omega: Vec<_> = (0..setup.n_omega()).map(|_| c.field()).collect();
        ensure!(!omega.contains(&L::ZERO), "G excluded omega");
        let mut req = vec![PCS_INIT];
        req.extend(1u64.to_le_bytes());
        wire::fields(&mut req, weights);
        wire::fields(&mut req, &omega);
        let hm = bus.sum(req, 1)?[0];
        let eps = tr.round(&ZERO, bytes(&[hm])).field();
        ensure!(eps != L::ZERO, "G excluded epsilon");
        (L::ZERO, vec![], hm, eps, vec![])
    } else {
        let inst = instance.unwrap();
        let mut req = vec![PCS_INIT];
        req.extend(0u64.to_le_bytes());
        wire::fields(&mut req, &inst.r_h);
        wire::fields(&mut req, &inst.r_a);
        wire::fields(&mut req, &inst.r_b);
        wire::field(&mut req, inst.s_x);
        let xi = bus.sum(req, 1)?[0];
        let alpha = tr.round(&roots[0], bytes(&[xi])).field();
        let t = bus.sum(wire::command(PCS_FRONTEND, &[alpha]), D)?;
        let mut c = tr.round(&dummy, bytes(&t));
        let r_pp: Vec<_> = (0..8).map(|_| c.field()).collect();
        let omega: Vec<_> = (0..setup.n_omega()).map(|_| c.field()).collect();
        let mut req = vec![PCS_MASK];
        wire::fields(&mut req, &omega);
        let hm = bus.sum(req, 1)?[0];
        let eps = tr.round(&dummy, bytes(&[hm])).field();
        (xi, t, hm, eps, r_pp)
    };
    let mut req = wire::command(PCS_WEIGHTS, &[eps]);
    if !is_g {
        wire::fields(&mut req, &r_pp);
    }
    ensure!(
        bus.all(req)?.iter().all(Vec::is_empty),
        "PCS weights response"
    );
    let mut coeffs = Vec::new();
    for j in 0..setup.params.folds() {
        let v = bus.sum(vec![PCS_ROUND], 2)?;
        coeffs.push((v[0], v[1]));
        let root = if j == 0 {
            if is_g { &ZERO } else { &dummy }
        } else {
            &roots[j]
        };
        let r = tr.round(root, bytes(&v)).field();
        if is_g {
            ensure!(r != L::ONE, "G excluded fold");
        }
        let reply = bus.all(wire::command(PCS_FOLD, &[r]))?;
        if j + 1 < setup.params.folds() {
            let top = Tree::build(&h.at_layer((j + 1) as u64), collect_hashes(reply)?);
            roots.push(top.root());
            tops.push(top);
        } else {
            ensure!(reply.iter().all(Vec::is_empty), "last fold response");
        }
    }
    let tail_root = Tree::build(
        &h.at_layer(protocol::TAG_TAIL),
        collect_hashes(bus.all(vec![PCS_TAIL])?)?,
    )
    .root();
    let queries = protocol::sample_queries(setup, tr, &tail_root);
    let mut by_party = vec![Vec::new(); setup.params.n_parties];
    for (a, &(i, q)) in queries.iter().enumerate() {
        by_party[i].push((a, q));
    }
    let req = by_party
        .iter()
        .map(|qs| {
            let mut b = vec![PCS_QUERIES];
            b.extend((qs.len() as u64).to_le_bytes());
            for &(_, q) in qs {
                b.extend((q as u64).to_le_bytes());
            }
            b
        })
        .collect();
    let responses = bus.exchange(req)?;
    let mut tails = vec![];
    let mut tail_salts = vec![];
    let mut openings: Vec<Vec<Opening>> = vec![vec![]; queries.len()];
    for (i, b) in responses.iter().enumerate() {
        let mut r = Reader(b);
        let tail = r.fields()?;
        ensure!(
            tail.len() == 1 << setup.params.tau,
            "terminal coefficients shape"
        );
        tails.push(tail);
        tail_salts.push(r.hash()?);
        ensure!(
            r.u64()? as usize == by_party[i].len(),
            "query response count"
        );
        for &(a, _) in &by_party[i] {
            for j in 0..setup.params.folds() {
                let values = [r.field()?, r.field()?];
                let salt = r.hash()?;
                let len = r.u64()? as usize;
                ensure!(len == setup.params.m() - j - 1, "query local path length");
                let mut path = (0..len).map(|_| r.hash()).collect::<Result<Vec<_>>>()?;
                path.extend(tops[j].path(i));
                openings[a].push(Opening { values, salt, path });
            }
        }
        r.finish()?;
    }
    Ok(Proof {
        roots,
        tail_root,
        xi,
        t,
        h_omega,
        coeffs,
        tails,
        tail_salts,
        openings,
    })
}

pub fn run(out: &Path, address: &str) -> Result<()> {
    run_with_mode(out, address, MatrixMode::Indexed)
}

pub fn run_with_mode(out: &Path, address: &str, mode: MatrixMode) -> Result<()> {
    run_internal(out, address, mode, None, false)
}

pub fn simulate(out: &Path, trace: &Path) -> Result<()> {
    run_internal(out, "", MatrixMode::Structured, Some(trace), false)
}

pub fn simulate_isolated(out: &Path, trace: &Path) -> Result<()> {
    run_internal(out, "", MatrixMode::Structured, Some(trace), true)
}

fn run_internal(out: &Path, address: &str, mode: MatrixMode, trace: Option<&Path>, isolated: bool) -> Result<()> {
    let prep = Instant::now();
    let shape = Shape::read(out)?;
    let data = fs::read(out.join("statement.bin"))?;
    ensure!(data.len() == shape.messages * 32, "public digest count");
    let digests: Vec<[u8; 32]> = data
        .chunks_exact(32)
        .map(|d| d.try_into().unwrap())
        .collect();
    let cfg=Arc::new(PublicPreprocessing::new(shape.config()?,digests.clone()));
    // The structured path never builds or commits a generic sparse index.
    let index = (mode == MatrixMode::Indexed).then(|| Index::new(&cfg, shape.gamma));
    let structured = if mode == MatrixMode::Structured {
        Some(StructuredKey::new(
            shape.application, shape.parties, cfg.groups, shape.gamma, shape.tau,
        ).map_err(anyhow::Error::msg)?)
    } else { None };
    let key = if let Some(index) = &index {
        crate::indexed_codec::encode_key(&index.verifier_key(&cfg))
    } else {
        structured.as_ref().unwrap().encode()
    };
    fs::write(out.join("key.bin"), &key)?;
    let statement = if let Some(index) = &index {
        index.statement(&cfg, &digests)
    } else {
        structured.as_ref().unwrap().statement(&digests)
    };
    let public_preprocessing_seconds=prep.elapsed().as_secs_f64();
    let common_public_cache_payload_bytes=cfg.cache_payload_bytes();
    let key_public_cache_payload_bytes=structured.as_ref().map_or(0,|key|context_cache_payload_bytes(key.config()));
    let public_cache_payload_bytes=common_public_cache_payload_bytes+key_public_cache_payload_bytes+fixed_interpolation_payload_bytes()+statement.len();
    println!("{}",serde_json::json!({"event":"public_preprocessing_complete","seconds":public_preprocessing_seconds,"added_public_cache_payload_bytes":public_cache_payload_bytes,"common_public_tables_payload_bytes":common_public_cache_payload_bytes,"canonical_key_extra_cache_payload_bytes":key_public_cache_payload_bytes,"statement_payload_bytes":statement.len(),"fixed_interpolation_payload_bytes":fixed_interpolation_payload_bytes(),"payload_scope":"extra public tables held by simulator coordinator; shared common tables counted once; excludes original NTT/layouts, Vec headers, capacity and allocator overhead; not cluster/per-party RAM","private_material_reused":false,"public_config_shared_only_in_sequential_simulation":trace.is_some()}));
    let mut bus = if let Some(trace) = trace {
        Bus { peers: vec![], simulation: Some(crate::simulation::Simulation::new(out, trace,Arc::clone(&cfg),isolated)?),
              sent: 0, received: 0, frames: 0, rounds: 0 }
    } else {
        Bus::accept(address, shape.parties)?
    };
    let preparation_seconds = prep.elapsed().as_secs_f64();
    println!(
        "{}",
        serde_json::json!({"event":"online_start","all_parties_ready":true,"development":shape.development})
    );
    std::io::stdout().flush()?;
    let online = Instant::now();
    if let Some(sim) = &mut bus.simulation { sim.begin(); }
    let start = bus.all(vec![START])?;
    let mut main_roots = vec![];
    let mut g_roots = vec![];
    let (mut nonce, mut h1) = (L::ZERO, L::ZERO);
    for b in &start {
        let mut r = Reader(b);
        main_roots.push(r.hash()?);
        g_roots.push(r.hash()?);
        nonce += r.field()?;
        h1 += r.field()?;
        r.finish()?;
    }
    let main_root = Tree::build(
        &Hasher::<H>::scoped(zk::BIT_ROLE).at_layer(0),
        main_roots.clone(),
    )
    .root();
    let g_root = Tree::build(
        &Hasher::<H>::scoped(zk::G_ROLE).at_layer(0),
        g_roots.clone(),
    )
    .root();
    let h = Hasher::<H>::default();
    let top = h.hash(&[b"v04-top", &main_root, &g_root]);
    let nonce: Hash = bytemuck::cast(nonce);

    let mut tr = Transcript::new_global(&h, &statement);
    tr.absorb(b"initial roots", &[main_root, g_root].concat());
    let mut c = tr.round(&top, &nonce);
    let tau: Vec<_> = (0..cfg.sc1_len()).map(|_| c.field()).collect();
    bus.empty(SC1_INIT, &tau)?;
    let lambda1 = tr.round(&ZERO, bytes(&[h1])).field();
    ensure!(lambda1 != L::ZERO, "SC1 lambda zero");
    let mut claim = lambda1 * h1;
    let nv = cfg.circuit.base.log_m0 + cfg.groups.trailing_zeros() as usize;
    let mut sc1 = vec![];
    let mut rcol = vec![];
    for _ in 0..nv {
        let v = bus.sum(wire::command(SC1_COL_ROUND, &[lambda1]), 4)?;
        ensure!(v[0] + v[1] == claim, "SC1 column consistency");
        let r = tr.round(&ZERO, bytes(&v)).field();
        ensure!(r != L::ONE, "SC1 excluded challenge");
        claim = interp(&v, r);
        sc1.push(v.try_into().unwrap());
        rcol.push(r);
        bus.empty(SC1_COL_FOLD, &[r])?;
    }
    let masked = bus.all(vec![CONVERSION_MASK])?;
    let mut conversions = vec![vec![L::ZERO; shape.parties]; 2];
    for (i, b) in masked.iter().enumerate() {
        let v = wire::scalars(b, 2)?;
        for a in 0..2 {
            conversions[a][i] = v[a];
        }
    }
    let mut deltas = Vec::new();
    for values in &conversions {
        deltas.extend(cfg.ctx.open_packed(values));
    }
    bus.empty(CONVERSION_OPEN, &deltas)?;
    tr.absorb(b"conversions", bytes(&conversions.concat()));
    let mut ry = vec![];
    for _ in 0..cfg.pcs.log_k() {
        let v = bus.sum(wire::command(SC1_SLOT_ROUND, &[lambda1]), 4)?;
        ensure!(v[0] + v[1] == claim, "SC1 slot consistency");
        let r = tr.round(&ZERO, bytes(&v)).field();
        ensure!(r != L::ONE, "SC1 excluded challenge");
        claim = interp(&v, r);
        sc1.push(v.try_into().unwrap());
        ry.push(r);
        bus.empty(SC1_SLOT_FOLD, &[r])?;
    }
    let ep = bus.sum(vec![SC1_ENDPOINT], 4)?;
    let endpoints = [ep[0], ep[1], ep[2]];
    let y1 = ep[3];
    let rx: Vec<_> = rcol.iter().chain(&ry).copied().collect();
    ensure!(
        claim == eq_eval(&tau, &rx) * (endpoints[0] * endpoints[1] + endpoints[2]) + lambda1 * y1,
        "SC1 endpoint consistency"
    );
    let mut c = tr.round(&ZERO, bytes(&ep));
    let rho = [c.field(), c.field(), c.field()];
    let (mut weights, public) = cfg.weight_values(&rcol, &ry, rho);
    let public_proof = index.as_ref().map(|index| {
        let input = indexed::public_vector(cfg.groups, cfg.ctx.k, &ry, &digests, cfg.circuit.keccak);
        crate::sparse_matrix::contract_prove(&index.public, &rcol, rho, &input, public, &mut tr)
    });
    let h2 = bus.sum(wire::command(SC2_INIT, &rho), 1)?[0];
    let lambda2 = tr.round(&ZERO, bytes(&[h2])).field();
    ensure!(lambda2 != L::ZERO, "SC2 lambda zero");
    let mut claim2: L =
        rho.iter().zip(endpoints).map(|(&a, b)| a * b).sum::<L>() + public + lambda2 * h2;
    let mut sc2 = vec![];
    let mut rp = vec![];
    for _ in 0..cfg.sc2_len() {
        let v = bus.sum(wire::command(SC2_ROUND, &[lambda2]), 3)?;
        ensure!(v[0] + v[1] == claim2, "SC2 consistency");
        let r = tr.round(&ZERO, bytes(&v)).field();
        ensure!(r != L::ONE, "SC2 excluded challenge");
        claim2 = interp(&v, r);
        sc2.push(v.try_into().unwrap());
        rp.push(r);
        let pairs = &cfg.sc2_schedule[rp.len()-1];
        weights = sparse_fold(&weights, pairs, r);
        bus.empty(SC2_FOLD, &[r])?;
    }
    let v = bus.sum(vec![SC2_ENDPOINT], 2)?;
    let (value, y2) = (v[0], v[1]);
    ensure!(
        claim2 == weights[0] * value + lambda2 * y2,
        "SC2 endpoint consistency"
    );
    let private_proof = index.as_ref().map(|index| {
        tr.absorb(b"private matrix endpoint", bytes(&[weights[0], value, y2]));
        crate::sparse_matrix::prove(&index.private, &rcol, &rp, rho, weights[0], &mut tr)
    });
    let eta = tr.round(&ZERO, bytes(&[value, y2])).field();
    let mut gw = zk::selector_weights(&rx, 3);
    gw.extend(zk::selector_weights(&rp, 2).into_iter().map(|x| eta * x));
    let g = open(
        &mut bus,
        &cfg.g,
        g_roots,
        &mut tr,
        Some((&cfg.gmap, &gw)),
        None,
    )?;
    tr.absorb(b"G opening", &sha_zk::encode_pcs(&g));
    let inst = Instance {
        r_h: rp[..8].to_vec(),
        r_a: ry,
        r_b: rp[8..].to_vec(),
        s_x: value,
    };
    tr.absorb(b"main instance", &inst.to_bytes());
    let pcs = open(&mut bus, &cfg.pcs, main_roots, &mut tr, None, Some(&inst))?;
    let proof = sha_zk::Proof {
        nonce,
        top,
        h1,
        h2,
        y1,
        y2,
        conversions,
        g,
        sc1,
        endpoints,
        sc2,
        value,
        pcs,
    };
    let (proof_bytes, format) = if let Some(key) = &structured {
        key.encode_proof(&proof)
    } else {
        let matrix = MatrixProof {
            public_value: public,
            input: public_proof.unwrap(),
            weight: weights[0],
            private: private_proof.unwrap(),
        };
        (crate::indexed_codec::encode_proof(&proof, &matrix), "B2IDX005")
    };
    if let Some(sim) = &mut bus.simulation { sim.finish()?; }
    let online_ns = online.elapsed().as_nanos() as u64;
    let online_seconds = online_ns as f64 / 1e9;
    let mut record = serde_json::json!({"phase":"online_proving","online_seconds":online_seconds,"online_ns":online_ns,"coordinator_preparation_seconds":preparation_seconds,"public_preprocessing_seconds":public_preprocessing_seconds,"added_public_cache_payload_bytes":public_cache_payload_bytes,"common_public_tables_payload_bytes":common_public_cache_payload_bytes,"canonical_key_extra_cache_payload_bytes":key_public_cache_payload_bytes,"proof_bytes":proof_bytes.len(),"online_payload_sent_by_coordinator":bus.sent,"online_payload_sent_by_parties":bus.received,"online_framing_bytes":bus.frames,"online_exchange_rounds":bus.rounds,"development":shape.development,"private_state_files_read_by_coordinator":0,"complete_proof_format":format,"matrix_mode":mode.name(),"generic_matrix_authentication":index.is_some(),"verification_status":"pending_independent_process","formal_measurement":false,"per_party_affinity_and_namespace":"external_runner_must_verify"});
    if trace.is_some() {
        record["execution_mode"] = if isolated {"persistent-worker-process-sequential-simulation"} else {"single-process-sequential-simulation"}.into();
        record["private_state_files_read_by_coordinator"] = if isolated {0} else {shape.parties}.into();
        record["logical_coordinator_private_state_files_read"] = 0.into();
        record["private_state_counter_scope"] = if isolated {"parent loads zero Shares; each persistent child loads its own one; same-host OS account is not a security boundary"} else {"simulation harness hosts all workers; no process privacy isolation"}.into();
        record["per_party_affinity_and_namespace"] = "sequential backend pinned externally; virtual party cores modeled offline".into();
    }
    println!(
        "{}",
        serde_json::json!({"event":"online_end","online_seconds":online_seconds,"proof_bytes":proof_bytes.len()})
    );
    std::io::stdout().flush()?;
    bus.empty(STOP, &[])?;
    if let Some(sim)=&bus.simulation {record["simulation_backend"]=sim.metadata();}
    fs::write(out.join("proof.bin"), proof_bytes)?;
    fs::write(out.join("prove.json"), serde_json::to_vec_pretty(&record)?)?;
    Ok(())
}
pub fn verify(out: &Path) -> Result<()> {
    let prep = Instant::now();
    let key_bytes = fs::read(out.join("key.bin"))?;
    let proof_bytes = fs::read(out.join("proof.bin"))?;
    let d = fs::read(out.join("statement.bin"))?;
    let structured = key_bytes.starts_with(b"KEYKEC01") || key_bytes.starts_with(b"KEYSHA03");
    let indexed_key = if structured { None } else {
        Some(crate::indexed_codec::decode_key(&key_bytes).map_err(anyhow::Error::msg)?)
    };
    let structured_key = if structured {
        Some(StructuredKey::decode(&key_bytes).map_err(anyhow::Error::msg)?)
    } else { None };
    let preparation_seconds = prep.elapsed().as_secs_f64();
    let start = Instant::now();
    let result = (|| {
        ensure!(d.len() % 32 == 0, "digest bytes");
        let digests: Vec<[u8; 32]> = d.chunks_exact(32).map(|v| v.try_into().unwrap()).collect();
        if let Some(key) = &structured_key {
            key.verify(&digests, &proof_bytes).map_err(anyhow::Error::msg)
        } else {
            let key = indexed_key.as_ref().unwrap();
            let (p, m) = crate::indexed_codec::decode_proof(key, &proof_bytes).map_err(anyhow::Error::msg)?;
            indexed::verify(key, &digests, &p, &m).map_err(anyhow::Error::msg)
        }
    })();
    let record = serde_json::json!({"accepted":result.is_ok(),"error":result.as_ref().err().map(ToString::to_string),"verify_seconds":start.elapsed().as_secs_f64(),"preparation_seconds":preparation_seconds,"private_input_read":false,"full_prover_index_read":false,"matrix_mode":if structured {"structured"}else{"indexed"},"fixed_base_circuit_rebuilt":structured,"generic_matrix_authentication":!structured,"formal_measurement":false});
    fs::write(out.join("verify.json"), serde_json::to_vec_pretty(&record)?)?;
    println!("{record}");
    result
}

#[cfg(test)]
mod indexed_keccak_tests {
    use super::*;
    struct Fixture(std::path::PathBuf);
    impl Drop for Fixture {fn drop(&mut self){let _=fs::remove_dir_all(&self.0);}}

    #[test]
    fn complete_indexed_keccak_proof_and_public_output_mutations() {
        let dir=std::env::temp_dir().join(format!("piop-indexed-keccak-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&dir).unwrap();let f=Fixture(dir);
        let input=f.0.join("input.bin");
        fs::write(&input,(0..400).map(|x|x as u8).collect::<Vec<_>>()).unwrap();
        let out=f.0.join("proof");
        crate::prepare::run(Shape{application:crate::application::Application::Keccak,layout_version:crate::prepare::LAYOUT_VERSION,parties:8,messages:2,gamma:16,tau:3,development:true},&input,&out).unwrap();
        run_internal(&out,"",MatrixMode::Indexed,Some(&f.0.join("trace.json")),false).unwrap();
        let key=fs::read(out.join("key.bin")).unwrap();
        assert_eq!(&key[..8],b"KEYKIDX1");
        let decoded=crate::indexed_codec::decode_key(&key).unwrap();
        assert!(decoded.keccak);
        assert_eq!(crate::indexed_codec::encode_key(&decoded),key);
        verify(&out).unwrap();
        let output=fs::read(out.join("statement.bin")).unwrap();
        for byte in [0,3,31,32,63] {
            let mut bad=output.clone();bad[byte]^=1;
            fs::write(out.join("statement.bin"),bad).unwrap();
            assert!(verify(&out).is_err(),"altered public output byte {byte}");
        }
        fs::write(out.join("statement.bin"),&output).unwrap();
        let mut wrong_key=key.clone();wrong_key[..8].copy_from_slice(b"KEYIDX04");
        fs::write(out.join("key.bin"),&wrong_key).unwrap();
        assert!(verify(&out).is_err(),"SHA output order must reject the Keccak proof");
        fs::write(out.join("key.bin"),key).unwrap();
        verify(&out).unwrap();
    }
}
