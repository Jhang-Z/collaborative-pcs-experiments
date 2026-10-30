//! A persistent party owns only its own private state. Every fold consumes a received challenge.
use crate::{
    field::{Field, L, eq_expand, from_b},
    merkle::Hasher,
    prepare::{self, Shape, Shares},
    protocol::{Challenges, Party, TAG_TAIL},
    setup::Instance,
    sha_spartan::{sparse_fold, sparse_round},
    preprocessing::{PublicPreprocessing,fixed_interpolation_payload_bytes},
    spartan::{fold_b, fold_l, round_b, round_l},
    wire::{self, Reader, *},
    zk,
};
use anyhow::{Result, bail, ensure};
use binius_hash::Blake3HashSuite as H;
use std::{
    fs,
    net::TcpStream,
    path::Path,
    time::{Duration, Instant},
    sync::Arc,
};

pub(crate) struct Worker {
    id: usize,
    cfg: Arc<PublicPreprocessing>,
    sh: Shares,
    pcs: [Party; 2],
    stage: u8,
    pending: bool,
    lag: L,
    mu: L,
    mu2: L,
    tau: Vec<L>,
    eq: Vec<L>,
    rows: [Vec<L>; 3],
    sss: [Vec<L>; 3],
    rcol: Vec<L>,
    ry: Vec<L>,
    rp: Vec<L>,
    z: Vec<L>,
    weights: Vec<L>,
    active: usize,
    pcs_step: u8,
    pcs_round: usize,
    inst: Option<Instance>,
    alpha: L,
    mw: Vec<(usize, L)>,
    gw: Vec<L>,
}
impl Worker {
    pub(crate) fn new(shape: Shape, id: usize, out: &Path) -> Result<Self> {
        let public_start=Instant::now();
        let data=fs::read(out.join("statement.bin"))?;
        ensure!(data.len()==shape.messages*32,"digest count");
        let digests=data.chunks_exact(32).map(|d|d.try_into().unwrap()).collect();
        let public=Arc::new(PublicPreprocessing::new(shape.config()?,digests));
        eprintln!("{}",serde_json::json!({"event":"worker_public_preprocessing_complete","party":id,"seconds":public_start.elapsed().as_secs_f64(),"added_public_cache_payload_bytes":public.cache_payload_bytes()+fixed_interpolation_payload_bytes(),"payload_scope":"this worker process only; excludes original NTT/layouts, Vec headers, capacity and allocator overhead","private_shares_loaded":false}));
        Self::with_preprocessing(id,out,public)
    }
    pub(crate) fn with_preprocessing(id:usize,out:&Path,cfg:Arc<PublicPreprocessing>)->Result<Self> {
        ensure!(id<cfg.ctx.n,"party id");
        let mut sh=Shares::read(&out.join(format!("party-{id}.private")),&cfg)?;
        let mut p = Party::new(id, cfg.pcs.params.n(), 0);
        p.row = std::mem::take(&mut sh.main);
        p.rng = prepare::entropy()?;
        p.prepare_salts(&cfg.pcs);
        let mut g = Party::new(id, cfg.g.params.n(), 0);
        g.row = std::mem::take(&mut sh.g);
        g.rng = prepare::entropy()?;
        g.prepare_salts(&cfg.g);
        let lag = cfg.lag_eta0[id];
        Ok(Self {
            id,
            cfg,
            sh,
            pcs: [p, g],
            stage: 0,
            pending: false,
            lag,
            mu: L::ZERO,
            mu2: L::ZERO,
            tau: vec![],
            eq: vec![],
            rows: std::array::from_fn(|_| vec![]),
            sss: std::array::from_fn(|_| vec![]),
            rcol: vec![],
            ry: vec![],
            rp: vec![],
            z: vec![],
            weights: vec![],
            active: 1,
            pcs_step: 0,
            pcs_round: 0,
            inst: None,
            alpha: L::ZERO,
            mw: vec![],
            gw: vec![],
        })
    }
    pub(crate) fn dispatch(&mut self, tag: u8, data: &[u8]) -> Result<Vec<u8>> {
        let mut r = Reader(data);
        let mut out = Vec::new();
        let nv = self.cfg.circuit.base.log_m0 + self.cfg.groups.trailing_zeros() as usize;
        match tag {
            START => {
                ensure!(self.stage == 0, "duplicate start");
                for (a, role) in [(0, zk::BIT_ROLE), (1, zk::G_ROLE)] {
                    let setup = if a == 0 { &self.cfg.pcs } else { &self.cfg.g };
                    let cw = setup.row.encode(&self.pcs[a].row);
                    self.pcs[a].commit_layer(setup, &Hasher::<H>::scoped(role), 0, cw);
                    out.extend(self.pcs[a].subtrees[0].root());
                }
                wire::field(&mut out, self.lag * self.sh.nonce);
                wire::field(&mut out, self.lag * self.sh.masks[0].sum());
                self.stage = 1;
            }
            SC1_INIT => {
                ensure!(self.stage == 1, "SC1 init stage");
                self.tau = (0..self.cfg.sc1_len())
                    .map(|_| r.field())
                    .collect::<Result<_>>()?;
                self.eq = eq_expand(&self.tau[..nv]);
                let ey = eq_expand(&self.tau[nv..]);
                self.mu = (0..self.cfg.ctx.k)
                    .map(|y| ey[y] * self.cfg.ctx.lag_n[self.id][y])
                    .sum();
                self.stage = 2;
            }
            SC1_COL_ROUND => {
                ensure!(
                    self.stage == 2 && !self.pending && self.rcol.len() < nv,
                    "SC1 column round order"
                );
                let lambda = r.field()?;
                let v = if self.rcol.is_empty() {
                    let [a, b, c] = &self.sh.piop.rows;
                    round_b(&self.eq, a, b, c)
                } else {
                    let [a, b, c] = &self.rows;
                    round_l(&self.eq, a, b, c)
                };
                let q = self.sh.masks[0].round(&self.rcol);
                for u in 0..4 {
                    wire::field(&mut out, self.mu * v[u] + lambda * self.lag * q[u]);
                }
                self.pending = true;
            }
            SC1_COL_FOLD => {
                ensure!(self.stage == 2 && self.pending, "SC1 column fold order");
                let x = r.field()?;
                ensure!(x != L::ONE, "excluded SC1 challenge");
                if self.rcol.is_empty() {
                    self.rows = std::array::from_fn(|a| fold_b(&self.sh.piop.rows[a], x));
                    for row in &mut self.sh.piop.rows {
                        *row = Vec::new();
                    }
                } else {
                    for row in &mut self.rows {
                        *row = fold_l(row, x);
                    }
                }
                self.eq = fold_l(&self.eq, x);
                self.rcol.push(x);
                self.pending = false;
                if self.rcol.len() == nv {
                    self.stage = 3;
                }
            }
            CONVERSION_MASK => {
                ensure!(self.stage == 3, "conversion mask order");
                for a in 0..2 {
                    wire::field(&mut out, self.rows[a][0] + self.sh.packed[a]);
                }
                self.stage = 4;
            }
            CONVERSION_OPEN => {
                ensure!(self.stage == 4, "conversion opening order");
                let k = self.cfg.ctx.k;
                for a in 0..2 {
                    self.sss[a] = (0..k)
                        .map(|y| r.field().map(|d| d + self.sh.ordinary[a][y]))
                        .collect::<Result<_>>()?;
                }
                self.sss[2] = (0..k)
                    .map(|y| {
                        self.cfg.conversion_weights[self.id][y] * self.rows[2][0]
                    })
                    .collect();
                let ecr = self.eq[0];
                self.eq = eq_expand(&self.tau[nv..])
                    .into_iter()
                    .map(|e| e * ecr)
                    .collect();
                self.rows = std::array::from_fn(|_| vec![]);
                self.stage = 5;
            }
            SC1_SLOT_ROUND => {
                ensure!(
                    self.stage == 5 && !self.pending && self.ry.len() < self.cfg.pcs.log_k(),
                    "SC1 slot round order"
                );
                let lambda = r.field()?;
                let [a, b, c] = &self.sss;
                let v = round_l(&self.eq, a, b, c);
                let prefix: Vec<_> = self.rcol.iter().chain(&self.ry).copied().collect();
                let q = self.sh.masks[0].round(&prefix);
                for u in 0..4 {
                    wire::field(&mut out, self.lag * (v[u] + lambda * q[u]));
                }
                self.pending = true;
            }
            SC1_SLOT_FOLD => {
                ensure!(self.stage == 5 && self.pending, "SC1 slot fold order");
                let x = r.field()?;
                ensure!(x != L::ONE, "excluded SC1 challenge");
                self.eq = fold_l(&self.eq, x);
                for v in &mut self.sss {
                    *v = fold_l(v, x);
                }
                self.ry.push(x);
                self.pending = false;
                if self.ry.len() == self.cfg.pcs.log_k() {
                    self.stage = 6;
                }
            }
            SC1_ENDPOINT => {
                ensure!(self.stage == 6, "SC1 endpoint order");
                for a in 0..3 {
                    wire::field(&mut out, self.lag * self.sss[a][0]);
                }
                let rx: Vec<_> = self.rcol.iter().chain(&self.ry).copied().collect();
                wire::field(&mut out, self.lag * self.sh.masks[0].value(&rx));
                self.stage = 7;
            }
            SC2_INIT => {
                ensure!(self.stage == 7, "SC2 init order");
                let rho = [r.field()?, r.field()?, r.field()?];
                let (w, _) = self.cfg.weight_values(&self.rcol, &self.ry, rho);
                self.weights = w;
                let ey = eq_expand(&self.ry);
                self.mu2 = (0..self.cfg.ctx.k)
                    .map(|y| ey[y] * self.cfg.ctx.lag_n[self.id][y])
                    .sum();
                for gg in 0..self.cfg.groups {
                    for p in 0..self.cfg.circuit.private_len {
                        self.z
                            .push(from_b(self.sh.piop.z[p + self.cfg.circuit.base.n0() * gg]));
                    }
                }
                self.sh.piop.z = Vec::new();
                wire::field(&mut out, self.lag * self.sh.masks[1].sum());
                self.stage = 8;
            }
            SC2_ROUND => {
                ensure!(
                    self.stage == 8 && !self.pending && self.rp.len() < self.cfg.sc2_len(),
                    "SC2 round order"
                );
                let lambda = r.field()?;
                let pairs = &self.cfg.sc2_schedule[self.rp.len()];
                let v = sparse_round(&self.weights, &self.z, &pairs);
                let q = self.sh.masks[1].round(&self.rp);
                for u in 0..3 {
                    wire::field(&mut out, self.mu2 * v[u] + lambda * self.lag * q[u]);
                }
                self.pending = true;
            }
            SC2_FOLD => {
                ensure!(self.stage == 8 && self.pending, "SC2 fold order");
                let x = r.field()?;
                ensure!(x != L::ONE, "excluded SC2 challenge");
                let pairs = &self.cfg.sc2_schedule[self.rp.len()];
                self.weights = sparse_fold(&self.weights, &pairs, x);
                self.z = sparse_fold(&self.z, &pairs, x);
                self.rp.push(x);
                self.pending = false;
                if self.rp.len() == self.cfg.sc2_len() {
                    self.stage = 9;
                }
            }
            SC2_ENDPOINT => {
                ensure!(self.stage == 9, "SC2 endpoint order");
                wire::field(&mut out, self.mu2 * self.z[0]);
                wire::field(&mut out, self.lag * self.sh.masks[1].value(&self.rp));
                self.z.clear();
                self.stage = 10;
            }
            PCS_INIT => {
                ensure!(self.stage == 10 && self.pcs_step == 0, "PCS init order");
                let a = r.u64()? as usize;
                ensure!(a == self.active, "PCS role order");
                if a == 1 {
                    self.gw = r.fields()?;
                    ensure!(self.gw.len() == self.cfg.gmap.len(), "G weights");
                    let omega = r.fields()?;
                    ensure!(omega.len() == self.cfg.g.n_omega(), "G omega");
                    self.mw = self.cfg.g.mask_weight(&omega);
                    wire::field(&mut out, self.pcs[1].h_omega(&self.cfg.g, &self.mw));
                    self.pcs_step = 3;
                } else {
                    let inst = Instance {
                        r_h: r.fields()?,
                        r_a: r.fields()?,
                        r_b: r.fields()?,
                        s_x: r.field()?,
                    };
                    ensure!(
                        inst.r_h.len() == 8
                            && inst.r_a.len() == self.cfg.pcs.log_k()
                            && inst.r_b.len() == self.cfg.pcs.params.ell,
                        "main instance shape"
                    );
                    wire::field(
                        &mut out,
                        self.pcs[0].frontend(&self.cfg.pcs, &inst, None)[0],
                    );
                    self.inst = Some(inst);
                    self.pcs_step = 1;
                }
            }
            PCS_FRONTEND => {
                ensure!(
                    self.stage == 10 && self.active == 0 && self.pcs_step == 1,
                    "PCS frontend order"
                );
                self.alpha = r.field()?;
                let v = self.pcs[0].frontend(
                    &self.cfg.pcs,
                    self.inst.as_ref().unwrap(),
                    Some(self.alpha),
                );
                out.extend_from_slice(bytemuck::cast_slice(&v));
                self.pcs_step = 2;
            }
            PCS_MASK => {
                ensure!(
                    self.stage == 10 && self.active == 0 && self.pcs_step == 2,
                    "PCS mask order"
                );
                let omega = r.fields()?;
                ensure!(omega.len() == self.cfg.pcs.n_omega(), "PCS omega");
                self.mw = self.cfg.pcs.mask_weight(&omega);
                wire::field(&mut out, self.pcs[0].h_omega(&self.cfg.pcs, &self.mw));
                self.pcs_step = 3;
            }
            PCS_WEIGHTS => {
                ensure!(self.stage == 10 && self.pcs_step == 3, "PCS weights order");
                let eps = r.field()?;
                if self.active == 1 {
                    ensure!(eps != L::ZERO, "G excluded epsilon");
                    let p = &mut self.pcs[1];
                    p.weight = vec![L::ZERO; self.cfg.g.params.n()];
                    let n=self.cfg.g.params.n();
                    for (&cell, &w) in self.cfg.gmap.iter().zip(&self.gw) {
                        p.weight[cell%n] += self.cfg.g.lagrange[self.id][cell/n] * w;
                    }
                    for &(x, w) in &self.mw {
                        p.weight[x] += self.cfg.g.lagrange[self.id][0] * eps * w;
                    }
                } else {
                    let r_pp = r.fields()?;
                    ensure!(r_pp.len() == 8, "PCS rpp");
                    let ch = Challenges {
                        alpha: self.alpha,
                        r_pp,
                        omega: vec![],
                        eps,
                        r: vec![],
                    };
                    self.pcs[0].weights(&self.cfg.pcs, self.inst.as_ref().unwrap(), &ch, &self.mw);
                }
                self.pcs_step = 4;
            }
            PCS_ROUND => {
                ensure!(
                    self.stage == 10 && self.pcs_step == 4 && !self.pending,
                    "PCS round order"
                );
                let (a, b) = self.pcs[self.active].round_poly();
                wire::field(&mut out, a);
                wire::field(&mut out, b);
                self.pending = true;
            }
            PCS_FOLD => {
                ensure!(
                    self.stage == 10 && self.pcs_step == 4 && self.pending,
                    "PCS fold order"
                );
                let x = r.field()?;
                if self.active == 1 {
                    ensure!(x != L::ONE, "G excluded fold");
                }
                let (setup, role) = if self.active == 1 {
                    (&self.cfg.g, zk::G_ROLE)
                } else {
                    (&self.cfg.pcs, zk::BIT_ROLE)
                };
                self.pcs[self.active].fold(setup, &Hasher::<H>::scoped(role), self.pcs_round, x);
                self.pcs_round += 1;
                if self.pcs_round < setup.params.folds() {
                    out.extend(self.pcs[self.active].subtrees[self.pcs_round].root());
                } else {
                    self.pcs_step = 5;
                }
                self.pending = false;
            }
            PCS_TAIL => {
                ensure!(self.stage == 10 && self.pcs_step == 5, "PCS tail order");
                let p = &self.pcs[self.active];
                let role = if self.active == 1 {
                    zk::G_ROLE
                } else {
                    zk::BIT_ROLE
                };
                out.extend(Hasher::<H>::scoped(role).at_layer(TAG_TAIL).leaf(
                    TAG_TAIL,
                    self.id as u64,
                    bytemuck::cast_slice(&p.row),
                    &p.tail_salt,
                ));
                self.pcs_step = 6;
            }
            PCS_QUERIES => {
                ensure!(self.stage == 10 && self.pcs_step == 6, "PCS queries order");
                let p = &self.pcs[self.active];
                wire::fields(&mut out, &p.row);
                out.extend(p.tail_salt);
                let count = r.u64()? as usize;
                let setup = if self.active == 1 {
                    &self.cfg.g
                } else {
                    &self.cfg.pcs
                };
                ensure!(count <= setup.params.gamma, "query count");
                out.extend((count as u64).to_le_bytes());
                for _ in 0..count {
                    let q = r.u64()? as usize;
                    ensure!(q < setup.params.fibres(0), "query index");
                    for j in 0..setup.params.folds() {
                        let x = q >> j;
                        out.extend_from_slice(bytemuck::cast_slice(
                            &p.codewords[j][2 * x..2 * x + 2],
                        ));
                        out.extend(p.salts[j][x]);
                        let path = p.subtrees[j].path(x);
                        out.extend((path.len() as u64).to_le_bytes());
                        for h in path {
                            out.extend(h);
                        }
                    }
                }
                self.pcs_round = 0;
                self.pcs_step = 0;
                if self.active == 1 {
                    self.active = 0;
                } else {
                    self.stage = 11;
                }
            }
            STOP => {
                ensure!(self.stage == 11, "stop before complete protocol");
                self.stage = 12;
            }
            _ => bail!("unknown command {tag}"),
        }
        r.finish()?;
        Ok(out)
    }
}
pub fn run(
    id: usize,
    out: &Path,
    address: &str,
    delay_command: Option<u8>,
    delay_ms: u64,
) -> Result<()> {
    let prep = Instant::now();
    let shape = Shape::read(out)?;
    let mut worker = Worker::new(shape, id, out)?;
    let connect_start = Instant::now();
    let mut s = loop {
        match TcpStream::connect(address) {
            Ok(s) => break s,
            Err(e) => {
                if connect_start.elapsed() > Duration::from_secs(3600) {
                    return Err(e.into());
                }
                std::thread::sleep(Duration::from_millis(100));
            }
        }
    };
    s.set_nodelay(true)?;
    let mut ready = b"FSREADY1".to_vec();
    ready.extend((id as u64).to_le_bytes());
    wire::send(&mut s, &ready)?;
    eprintln!(
        "{}",
        serde_json::json!({"role":"party","id":id,"event":"ready","preparation_seconds":prep.elapsed().as_secs_f64(),"pid":std::process::id(),"private_state_files_read":1})
    );
    let mut rounds = 0usize;
    loop {
        let msg = wire::receive(&mut s)?;
        ensure!(!msg.is_empty(), "empty command");
        let tag = msg[0];
        if delay_command == Some(tag) {
            std::thread::sleep(Duration::from_millis(delay_ms));
        }
        let reply = worker.dispatch(tag, &msg[1..])?;
        wire::send(&mut s, &reply)?;
        rounds += 1;
        if tag == STOP {
            break;
        }
    }
    eprintln!(
        "{}",
        serde_json::json!({"role":"party","id":id,"event":"complete","commands_consumed":rounds})
    );
    Ok(())
}

/// IPC metadata is simulator-only; protocol dispatch and its allocations stay timed.
pub fn run_stdio(id: usize, out: &Path) -> Result<()> {
    let prep=Instant::now();
    let shape=Shape::read(out)?;
    let worker=Worker::new(shape,id,out)?;
    stdio_loop(worker,prep)
}
/// Fork starts from public-only state; private shares/salts are loaded here,
/// independently in this worker. No party share is allocated in the parent.
pub(crate) fn run_stdio_with_public(id:usize,out:&Path,public:Arc<PublicPreprocessing>)->Result<()> {
    let prep=Instant::now();let worker=Worker::with_preprocessing(id,out,public)?;
    stdio_loop(worker,prep)
}
fn stdio_loop(mut worker:Worker,prep:Instant)->Result<()> {
    use std::io::Write;
    let id=worker.id;
    let ready=serde_json::json!({"role":"party","event":"ready","id":id,
        "pid":std::process::id(),"preparation_seconds":prep.elapsed().as_secs_f64(),
        "private_state_files_read":1,
        "added_public_cache_payload_bytes":worker.cfg.cache_payload_bytes()+fixed_interpolation_payload_bytes(),
        "memory":crate::simulation::process_memory(std::process::id())});
    eprintln!("{ready}");
    let mut ready_bytes=b"FSHEAP01".to_vec();
    ready_bytes.extend(serde_json::to_vec(&ready)?);
    let mut input=std::io::stdin().lock();
    let mut output=std::io::stdout().lock();
    wire::send(&mut output,&ready_bytes)?;
    output.flush()?;
    loop {
        let request=wire::receive(&mut input)?;
        ensure!(!request.is_empty(),"empty stdio command");
        let tag=request[0];
        let start=Instant::now();
        let reply=worker.dispatch(tag,&request[1..])?;
        let elapsed=start.elapsed().as_nanos() as u64;
        wire::send(&mut output,&reply)?;
        // Extra IPC copies are freed before the timing footer completes the exchange.
        drop(reply);
        drop(request);
        output.write_all(&elapsed.to_le_bytes())?;
        if tag==STOP {
            wire::send(&mut output,&serde_json::to_vec(&crate::simulation::process_memory(std::process::id()))?)?;
        }
        output.flush()?;
        if tag==STOP {break;}
    }
    Ok(())
}
