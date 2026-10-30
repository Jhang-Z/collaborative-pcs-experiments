//! Executable, non-ZK collaborative SHA/Spartan/PCS spine.
//! All parties run sequentially in this process; aggregation is ideal/plaintext.
//! No complete zkSNARK or distributed latency claim is made by this module.
use crate::{
	field::{B, D, Field, L, Random, eq_expand, from_b, from_words, mul_b},
	fs::Transcript,
	merkle::{Hash, Hasher},
	params::{Params, ell_for_bits},
	protocol::{self, Proof as PcsProof},
	setup::{Instance, Setup, Witness},
	sha_circuit::ShaCircuit,
	spartan::{Ctx, PTimes, PartyShares, eq_eval, fold_b, fold_l, interp, omega, round_b, round_l},
};
use binius_field::arithmetic_traits::InvertOrZero;
use binius_hash::Blake3HashSuite as H;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};
const DOMAIN: &[u8] = b"sha256-32-byte-spartan-nonzk-v5-global-capacity-cubes-blake3";
const ZERO: Hash = [0; 32];

pub struct Config {
	pub circuit: ShaCircuit,
	pub pcs: Setup,
	pub ctx: Ctx,
	pub groups: usize,
	/// Physical (h,x) indices for one slot's logical wire vectors, including zero padding.
	pub map: Vec<usize>,
}

/// Public coefficients for the fixed repeated circuit, without expanding each group's bits.
pub(crate) struct MatrixWeights {
	pub(crate) base: Vec<L>,
	pub(crate) groups: Vec<L>,
	pub(crate) public: L,
}
impl MatrixWeights {
	/// Evaluate the private matrix at its physical (bit, column) address.
	/// Config's allocator preserves the low eight address bits, including across mask gaps.
	pub(crate) fn evaluate(&self, cfg: &Config, point: &[L]) -> L {
		assert_eq!(point.len(), cfg.sc2_len());
		let eh = eq_expand(&point[..8]);
		let ex = eq_expand(&point[8..]);
		let n0 = cfg.circuit.base.n0();
		self.base[..cfg.circuit.private_len]
			.chunks(D)
			.enumerate()
			.map(|(c, chunk)| {
				let alpha: L = chunk.iter().zip(&eh).map(|(&a, &h)| a * h).sum();
				let beta: L = self.groups.iter().enumerate().map(|(g, &eg)| {
					let address = cfg.map[g * n0 + c * D];
					debug_assert_eq!(address % D, 0);
					eg * ex[address / D]
				}).sum();
				alpha * beta
			})
			.sum()
	}
}
impl Config {
	pub fn new(n:usize,groups:usize,gamma:usize,tau:usize)->Self {Self::new_mode(n,groups,gamma,tau,false)}
 pub fn new_zk(n:usize,groups:usize,gamma:usize,tau:usize)->Self {Self::new_mode(n,groups,gamma,tau,true)}
 fn new_mode(n: usize, groups: usize, gamma: usize, tau: usize,zk:bool) -> Self {
		assert!(n >= 8 && n <= 256 && n.is_power_of_two());
		assert!(groups.is_power_of_two());
		let circuit = if zk {ShaCircuit::new_zk()}else{ShaCircuit::new()};
  Self::from_circuit(n,groups,gamma,tau,circuit)
 }
 pub fn from_circuit(n:usize,groups:usize,gamma:usize,tau:usize,circuit:ShaCircuit)->Self {
  assert!(n>=8&&n<=256&&n.is_power_of_two()&&groups.is_power_of_two());
  let zk=circuit.mask_start.is_some();
		let bits = circuit.base.n0() * groups;
		let mut ell = ell_for_bits(n, gamma, tau, 2, bits * (n / 4));
		let (pcs, map) = loop {
			let setup = Setup::new(Params {
				n_parties: n,
				ell,
				beta: 2,
				gamma,
				tau,
				salt_bytes: 32,
			});
            let mut theta_columns=vec![false;setup.params.n()];
            for m in setup.layout.masks.iter().flatten() {theta_columns[m.x]=true;}
            let cols:Vec<usize>=setup.layout.owned.iter().flatten().copied()
                .filter(|&x|!theta_columns[x]).collect();
   if cols.len()*D>=bits {
    if !zk {let map=(0..bits).map(|i|cols[i/D]*D+i%D).collect();break(setup,map)}
    // A physical mask block is any ten-coordinate cube: eight element bits
    // and two public column axes. Its logical row addresses stay unchanged.
    let mut cubes=Vec::<[usize;4]>::new();
    'axes: for a in 0..ell { for b in a+1..ell {
     cubes.clear();
     let axes=(1<<a)|(1<<b);
     for &x in &cols {
      if x&axes!=0 {continue;}
      let cube=[x,x^(1<<a),x^(1<<b),x^axes];
      if cube.iter().all(|c|cols.binary_search(c).is_ok()) {cubes.push(cube);}
      if cubes.len()==4*groups {break 'axes;}
     }
    }}
    if cubes.len()==4*groups {
     let mut reserved=vec![false;setup.params.n()];
     let mut map=vec![0;bits];
     let start=circuit.mask_start.unwrap().0;
     let n0=circuit.base.n0();
     for (i,cube) in cubes.iter().enumerate() {
      for &x in cube {reserved[x]=true;}
      let at=(i/4)*n0+start+(i%4)*1024;
      for h in 0..1024 {map[at+h]=cube[h/D]*D+h%D;}
     }
     let mut ordinary=cols.iter().copied().filter(|&x|!reserved[x]);
     for at in (0..bits).step_by(D) {
      let logical=at%n0;
      if logical>=start&&logical<start+4096 {continue;}
      let x=ordinary.next().expect("capacity includes reserved cubes");
      for h in 0..D {map[at+h]=x*D+h;}
     }
     break(setup,map)
    }
   }
			ell += 1;
		};
		Self {
			circuit,
			pcs,
			ctx: Ctx::new(n),
			groups,
			map,
		}
	}
	pub fn batch(&self) -> usize {
		self.groups * self.ctx.k
	}
	pub fn sc1_len(&self) -> usize {
		self.circuit.base.log_m0 + self.groups.trailing_zeros() as usize + self.pcs.log_k()
	}
	pub fn sc2_len(&self) -> usize {
		8 + self.pcs.params.ell
	}
	pub(crate) fn statement(&self, digests: &[[u8; 32]]) -> Vec<u8> {
		let mut out = if self.circuit.keccak {b"keccak-f1600-truncated256-layout-v1".to_vec()}else{DOMAIN.to_vec()};
		for n in [
			self.ctx.n,
			self.groups,
			self.pcs.params.ell,
			self.pcs.params.gamma,
			self.pcs.params.tau,
			self.pcs.params.beta,
			self.circuit.private_len,
			self.circuit.base.m0(),
			self.circuit.base.n0(),
		] {
			out.extend_from_slice(&(n as u64).to_le_bytes());
		}
		for d in digests {
			out.extend_from_slice(d);
		}
		out
	}
	pub(crate) fn matrix_weights(&self, rcol: &[L], ry: &[L], rho: [L; 3], digests: &[[u8; 32]]) -> MatrixWeights {
		let base = &self.circuit.base;
		assert_eq!(rcol.len(), base.log_m0 + self.groups.trailing_zeros() as usize);
		assert_eq!(ry.len(), self.pcs.log_k());
		assert_eq!(digests.len(), self.batch());
		let coefficients = base.weight(&eq_expand(&rcol[..base.log_m0]), rho);
		let groups = eq_expand(&rcol[base.log_m0..]);
		let slots = eq_expand(ry);
		let mut public = L::ZERO;
		for (y, &ey) in slots.iter().enumerate() {
			for (g, &eg) in groups.iter().enumerate() {
				let sum: L = self.circuit.public(&digests[g + self.groups * y])
					.into_iter().enumerate().filter(|(_, bit)| *bit)
					.map(|(i, _)| coefficients[self.circuit.private_len + i]).sum();
				public += ey * eg * sum;
			}
		}
		MatrixWeights { base: coefficients, groups, public }
	}
	pub(crate) fn weights(&self, rcol: &[L], ry: &[L], rho: [L; 3], digests: &[[u8; 32]]) -> (Vec<usize>, Vec<L>, L) {
		let base = &self.circuit.base;
		let w0 = base.weight(&eq_expand(&rcol[..base.log_m0]), rho);
		let eg = eq_expand(&rcol[base.log_m0..]);
		let ey = eq_expand(ry);
		let mut indices = Vec::new();
		let mut w = Vec::new();
		for gg in 0..self.groups {
			for p in 0..self.circuit.private_len {
				indices.push(self.map[p + base.n0() * gg]);
				w.push(w0[p] * eg[gg]);
			}
		}
		let mut public = L::ZERO;
		for y in 0..self.ctx.k {
			for gg in 0..self.groups {
				let pp = self.circuit.public(&digests[gg + self.groups * y]);
				let sum: L = pp
					.iter()
					.enumerate()
					.filter(|(_, v)| **v)
					.map(|(i, _)| w0[self.circuit.private_len + i])
					.sum();
				public += ey[y] * eg[gg] * sum;
			}
		}
		(indices, w, public)
	}
}
#[derive(Clone)]
pub struct Proof {
	pub sc1: Vec<[L; 4]>,
	pub endpoints: [L; 3],
	pub sc2: Vec<[L; 3]>,
	pub value: L,
	pub pcs: PcsProof,
}
#[derive(Default)]
pub struct Times {
	pub witness: Duration,
	pub piop_share: Duration,
	pub pcs_prepare: Duration,
	pub pcs_random: Duration,
	pub pcs_share: Duration,
	pub piop: Duration,
	pub conversion_preprocess: Duration,
	pub conversion_online: Duration,
	pub pcs_open: Duration,
	pub verify: Duration,
	pub total: Duration,
	pub parties: Vec<PTimes>,
}
pub struct Run {
	pub proof: Proof,
	pub digests: Vec<[u8; 32]>,
	pub times: Times,
}
fn bytes(v: &[L]) -> &[u8] {
	bytemuck::cast_slice(v)
}

pub fn prove(cfg: &Config, seed: u64) -> Run {
	let total = Instant::now();
	let mut tm = Times::default();
	let (ctx, base, g) = (&cfg.ctx, &cfg.circuit.base, cfg.groups);
	let (n, k, n0, m0) = (ctx.n, ctx.k, base.n0(), base.m0());
	let mut rng = StdRng::seed_from_u64(seed);
	let t = Instant::now();
	let copies: Vec<_> = (0..cfg.batch())
		.map(|_| {
			let mut msg = [0u8; 32];
			rng.fill_bytes(&mut msg);
			let c = cfg.circuit.witness(&msg);
			assert_eq!(c.2.as_slice(), Sha256::digest(msg).as_slice());
			c
		})
		.collect();
	let digests: Vec<_> = copies.iter().map(|c| c.2).collect();
	tm.witness = t.elapsed();
	let t = Instant::now();
	let mut parties: Vec<_> = (0..n)
		.map(|_| PartyShares {
			z: vec![B::ZERO; n0 * g],
			rows: std::array::from_fn(|_| vec![B::ZERO; m0 * g]),
		})
		.collect();
	let mut buf = vec![B::ZERO; n];
	for gg in 0..g {
		for p in 0..cfg.circuit.private_len {
			ctx.share_bits(|y| copies[gg + g * y].0[p], &mut rng, &mut buf);
			for i in 0..n {
				parties[i].z[p + n0 * gg] = buf[i];
			}
		}
		for a in 0..3 {
			for j in 0..m0 {
				ctx.share_bits(|y| copies[gg + g * y].1[a][j], &mut rng, &mut buf);
				for i in 0..n {
					parties[i].rows[a][j + m0 * gg] = buf[i];
				}
			}
		}
	}
	tm.piop_share = t.elapsed();
	let t = Instant::now();
	let cols = cfg.pcs.params.n();
	let mut packed = vec![[0u128; 2]; k * cols];
	for y in 0..k {
		for gg in 0..g {
			for p in 0..cfg.circuit.private_len {
				if copies[gg + g * y].0[p] {
					let a = cfg.map[p + n0 * gg];
					let (h, x) = (a % D, a / D);
					packed[y * cols + x][h / 128] |= 1u128 << (h % 128);
				}
			}
		}
	}
	let mut wit = Witness {
		table: packed.into_iter().map(from_words).collect(),
	};
	for m in cfg.pcs.layout.masks.iter().flatten() {
		wit.table[m.y * cols + m.x] = L::random(&mut rng);
	}
	let prepared = protocol::prepare::<H>(&cfg.pcs, &wit, seed ^ 0x504353);
	tm.pcs_random = prepared.preprocessing;
	tm.pcs_share = prepared.client_share;
	tm.pcs_prepare = t.elapsed();
	let root = prepared.root;
	// From here onward the prover uses only server state/shares, not client plaintext.
	drop(wit);
	drop(copies);
	let hasher = Hasher::<H>::default();
	let mut tr = Transcript::new(&hasher, &cfg.statement(&digests));
	let mut initial = tr.round(&root, b"committed witness");
	let tau: Vec<L> = (0..cfg.sc1_len()).map(|_| initial.field()).collect();
	let nv_col = base.log_m0 + g.trailing_zeros() as usize;
	let (eq_col, eq_y) = (eq_expand(&tau[..nv_col]), eq_expand(&tau[nv_col..]));
	let mu: Vec<L> = (0..n).map(|i| (0..k).map(|y| eq_y[y] * ctx.lag_n[i][y]).sum()).collect();
	let mut pt = vec![PTimes::default(); n];
	let piop_start = Instant::now();
	let mut st: Vec<(Vec<L>, [Vec<L>; 3])> = (0..n).map(|_| (vec![], std::array::from_fn(|_| vec![]))).collect();
	let mut sc1 = Vec::new();
	let mut rcol = Vec::new();
	let mut claim = L::ZERO;
	for round in 0..nv_col {
		let mut agg = [L::ZERO; 4];
		for i in 0..n {
			let t = Instant::now();
			let s = if round == 0 {
				let [a, b, c] = &parties[i].rows;
				round_b(&eq_col, a, b, c)
			} else {
				let (e, [a, b, c]) = &st[i];
				round_l(e, a, b, c)
			};
			pt[i].sc1_col += t.elapsed();
			for u in 0..4 {
				agg[u] += mu[i] * s[u];
			}
		}
		assert_eq!(agg[0] + agg[1], claim, "SC1 column");
		let r = tr.round(&ZERO, bytes(&agg)).field();
		claim = interp(&agg, r);
		sc1.push(agg);
		rcol.push(r);
		for i in 0..n {
			let t = Instant::now();
			if round == 0 {
				let [a, b, c] = &parties[i].rows;
				st[i] = (fold_l(&eq_col, r), [fold_b(a, r), fold_b(b, r), fold_b(c, r)]);
			} else {
				let (e, [a, b, c]) = &st[i];
				st[i] = (fold_l(e, r), [fold_l(a, r), fold_l(b, r), fold_l(c, r)]);
			}
			pt[i].sc1_col += t.elapsed();
		}
	}
	let ecr = st[0].0[0];
	let lag = ctx.lag_eta0();
	let mut sss: Vec<[Vec<L>; 3]> = (0..n).map(|_| std::array::from_fn(|_| vec![L::ZERO; k])).collect();
	// Only A and B need degree-reduced ordinary shares. Each double sharing is fresh.
	for a in 0..2 {
		let t = Instant::now();
		let r: Vec<L> = (0..k).map(|_| L::random(&mut rng)).collect();
		let packed = ctx.share_packed(&r, &mut rng);
		let ordinary: Vec<_> = r.iter().map(|&v| ctx.share_sss(v, &mut rng)).collect();
		tm.conversion_preprocess += t.elapsed();
		let t = Instant::now();
		let masked: Vec<_> = (0..n).map(|i| st[i].1[a][0] + packed[i]).collect();
		let delta = ctx.open_packed(&masked);
		for i in 0..n {
			for y in 0..k {
				sss[i][a][y] = delta[y] + ordinary[y][i];
			}
		}
		tm.conversion_online += t.elapsed();
	}
	let t = Instant::now();
	for i in 0..n {
		for y in 0..k {
			sss[i][2][y] = ctx.lag_n[i][y] * lag[i].invert_or_zero() * st[i].1[2][0];
		}
	}
	tm.conversion_online += t.elapsed();
	let mut es: Vec<L> = eq_y.iter().map(|&v| v * ecr).collect();
	let mut ry = Vec::new();
	for _ in 0..cfg.pcs.log_k() {
		let mut agg = [L::ZERO; 4];
		for i in 0..n {
			let t = Instant::now();
			let [a, b, c] = &sss[i];
			let s = round_l(&es, a, b, c);
			pt[i].sc1_slot += t.elapsed();
			for u in 0..4 {
				agg[u] += lag[i] * s[u];
			}
		}
		assert_eq!(agg[0] + agg[1], claim, "SC1 slot");
		let r = tr.round(&ZERO, bytes(&agg)).field();
		claim = interp(&agg, r);
		sc1.push(agg);
		ry.push(r);
		es = fold_l(&es, r);
		for i in 0..n {
			let t = Instant::now();
			for v in &mut sss[i] {
				*v = fold_l(v, r);
			}
			pt[i].sc1_slot += t.elapsed();
		}
	}
	let endpoints: [L; 3] = std::array::from_fn(|a| (0..n).map(|i| lag[i] * sss[i][a][0]).sum());
	let rx: Vec<_> = rcol.iter().chain(&ry).copied().collect();
	assert_eq!(claim, eq_eval(&tau, &rx) * (endpoints[0] * endpoints[1] + endpoints[2]));
	let mut c = tr.round(&ZERO, bytes(&endpoints));
	let rho = std::array::from_fn(|_| c.field());
	let (mut indices, mut weights, public) = cfg.weights(&rcol, &ry, rho, &digests);
	let mut claim2: L = rho.iter().zip(endpoints).map(|(&a, b)| a * b).sum::<L>() + public;
	let ey = eq_expand(&ry);
	let mu2: Vec<L> = (0..n).map(|i| (0..k).map(|y| ey[y] * ctx.lag_n[i][y]).sum()).collect();
	let mut zs: Vec<Vec<L>> = parties
		.iter()
		.enumerate()
		.map(|(i, p)| {
			let t = Instant::now();
			let mut z = Vec::with_capacity(weights.len());
			for gg in 0..g {
				for j in 0..cfg.circuit.private_len {
					z.push(from_b(p.z[j + n0 * gg]));
				}
			}
			pt[i].sc2_prep += t.elapsed();
			z
		})
		.collect();
	drop(parties);
	drop(st);
	let mut sc2 = Vec::new();
	let mut rp = Vec::new();
	for _ in 0..cfg.sc2_len() {
		let (parents, pairs) = sparse_pairs(&indices);
		let mut agg = [L::ZERO; 3];
		for i in 0..n {
			let t = Instant::now();
			let s = sparse_round(&weights, &zs[i], &pairs);
			pt[i].sc2 += t.elapsed();
			for u in 0..3 {
				agg[u] += mu2[i] * s[u];
			}
		}
		assert_eq!(agg[0] + agg[1], claim2, "SC2");
		let r = tr.round(&ZERO, bytes(&agg)).field();
		claim2 = interp(&agg, r);
		sc2.push(agg);
		rp.push(r);
		weights = sparse_fold(&weights, &pairs, r);
		for i in 0..n {
			let t = Instant::now();
			zs[i] = sparse_fold(&zs[i], &pairs, r);
			pt[i].sc2 += t.elapsed();
		}
		indices = parents;
	}
	let value: L = (0..n).map(|i| mu2[i] * zs[i][0]).sum();
	assert_eq!(claim2, weights[0] * value);
	tr.round(&ZERO, bytes(&[value]));
	let context = tr.state();
	tm.piop = piop_start.elapsed();
	tm.parties = pt;
	let inst = Instance {
		r_h: rp[..8].to_vec(),
		r_a: ry,
		r_b: rp[8..].to_vec(),
		s_x: value,
	};
	let t = Instant::now();
	let (pcs, _, _) = protocol::open_prepared::<H>(&cfg.pcs, &inst, prepared, &context);
	tm.pcs_open = t.elapsed();
	let proof = Proof {
		sc1,
		endpoints,
		sc2,
		value,
		pcs,
	};
	let t = Instant::now();
	verify(cfg, &digests, &proof).expect("full spine verification");
	tm.verify = t.elapsed();
	tm.total = total.elapsed();
	Run { proof, digests, times: tm }
}

/// Reads no private witness, row values, server shares, RNG seed, or prover state.
pub fn verify(cfg: &Config, digests: &[[u8; 32]], proof: &Proof) -> Result<(), String> {
	if digests.len() != cfg.batch()
		|| proof.sc1.len() != cfg.sc1_len()
		|| proof.sc2.len() != cfg.sc2_len()
		|| proof.pcs.roots.len() != cfg.pcs.params.folds()
	{
		return Err("shape".into());
	}
	let h = Hasher::<H>::default();
	let mut tr = Transcript::new(&h, &cfg.statement(digests));
	let mut c = tr.round(&proof.pcs.roots[0], b"committed witness");
	let tau: Vec<_> = (0..cfg.sc1_len()).map(|_| c.field()).collect();
	let mut claim = L::ZERO;
	let mut rx = Vec::new();
	for s in &proof.sc1 {
		if s[0] + s[1] != claim {
			return Err("SC1 sum".into());
		}
		let r = tr.round(&ZERO, bytes(s)).field();
		claim = interp(s, r);
		rx.push(r);
	}
	let v = proof.endpoints;
	if claim != eq_eval(&tau, &rx) * (v[0] * v[1] + v[2]) {
		return Err("SC1 endpoint".into());
	}
	let nvcol = cfg.circuit.base.log_m0 + cfg.groups.trailing_zeros() as usize;
	let (rcol, ry) = rx.split_at(nvcol);
	let mut c = tr.round(&ZERO, bytes(&v));
	let rho: [L; 3] = std::array::from_fn(|_| c.field());
	let (indices, w, public) = cfg.weights(rcol, ry, rho, digests);
	let mut claim = rho.iter().zip(v).map(|(&a, b)| a * b).sum::<L>() + public;
	let mut rp = Vec::new();
	for s in &proof.sc2 {
		if s[0] + s[1] != claim {
			return Err("SC2 sum".into());
		}
		let r = tr.round(&ZERO, bytes(s)).field();
		claim = interp(s, r);
		rp.push(r);
	}
	let eh = eq_expand(&rp[..8]);
	let ex = eq_expand(&rp[8..]);
	let wr: L = indices.iter().zip(w).map(|(&i, a)| a * eh[i % D] * ex[i / D]).sum();
	if claim != wr * proof.value {
		return Err("SC2 endpoint".into());
	}
	tr.round(&ZERO, bytes(&[proof.value]));
	let inst = Instance {
		r_h: rp[..8].to_vec(),
		r_a: ry.to_vec(),
		r_b: rp[8..].to_vec(),
		s_x: proof.value,
	};
	protocol::verify_bound::<H>(&cfg.pcs, &inst, &proof.pcs, &tr.state())?;
	Ok(())
}

impl Proof {
	/// Literal wire encoding, no estimated/deduplicated Merkle proof size.
	pub fn to_bytes(&self) -> Vec<u8> {
		let mut out = b"B2SHA003".to_vec();
		for r in &self.sc1 {
			out.extend_from_slice(bytes(r));
		}
		out.extend_from_slice(bytes(&self.endpoints));
		for r in &self.sc2 {
			out.extend_from_slice(bytes(r));
		}
		out.extend_from_slice(bytes(&[self.value]));
		let p = &self.pcs;
		for r in &p.roots {
			out.extend_from_slice(r);
		}
		out.extend_from_slice(&p.tail_root);
		out.extend_from_slice(bytes(&[p.xi]));
		out.extend_from_slice(bytes(&p.t));
		out.extend_from_slice(bytes(&[p.h_omega]));
		for &(a, b) in &p.coeffs {
			out.extend_from_slice(bytes(&[a, b]));
		}
		for (t, s) in p.tails.iter().zip(&p.tail_salts) {
			out.extend_from_slice(bytes(t));
			out.extend_from_slice(s);
		}
		for query in &p.openings {
			for o in query {
				out.extend_from_slice(bytes(&o.values));
				out.extend_from_slice(&o.salt);
				for h in &o.path {
					out.extend_from_slice(h);
				}
			}
		}
		out
	}
	pub fn from_bytes(cfg: &Config, input: &[u8]) -> Result<Self, String> {
		struct Reader<'a>(&'a [u8]);
		impl Reader<'_> {
			fn take(&mut self, n: usize) -> Result<&[u8], String> {
				if self.0.len() < n {
					return Err("truncated proof".into());
				}
				let (a, b) = self.0.split_at(n);
				self.0 = b;
				Ok(a)
			}
			fn hash(&mut self) -> Result<Hash, String> {
				Ok(self.take(32)?.try_into().unwrap())
			}
			fn field(&mut self) -> Result<L, String> {
				let b = self.hash()?;
				Ok(from_words([
					u128::from_le_bytes(b[..16].try_into().unwrap()),
					u128::from_le_bytes(b[16..].try_into().unwrap()),
				]))
			}
			fn fields(&mut self, n: usize) -> Result<Vec<L>, String> {
				(0..n).map(|_| self.field()).collect()
			}
		}
		let mut r = Reader(input);
		if r.take(8)? != b"B2SHA003" {
			return Err("proof version".into());
		}
		let sc1 = (0..cfg.sc1_len())
			.map(|_| Ok(r.fields(4)?.try_into().unwrap()))
			.collect::<Result<_, String>>()?;
		let endpoints = r.fields(3)?.try_into().unwrap();
		let sc2 = (0..cfg.sc2_len())
			.map(|_| Ok(r.fields(3)?.try_into().unwrap()))
			.collect::<Result<_, String>>()?;
		let value = r.field()?;
		let p = &cfg.pcs.params;
		let f = p.folds();
		let roots = (0..f).map(|_| r.hash()).collect::<Result<_, _>>()?;
		let tail_root = r.hash()?;
		let xi = r.field()?;
		let t = r.fields(D)?;
		let h_omega = r.field()?;
		let coeffs = (0..f).map(|_| Ok((r.field()?, r.field()?))).collect::<Result<_, String>>()?;
		let (mut tails, mut tail_salts) = (Vec::new(), Vec::new());
		for _ in 0..p.n_parties {
			tails.push(r.fields(1 << p.tau)?);
			tail_salts.push(r.hash()?);
		}
		let mut openings = Vec::new();
		for _ in 0..p.gamma {
			let mut ops = Vec::new();
			for j in 0..f {
				let values = r.fields(2)?.try_into().unwrap();
				let salt = r.hash()?;
				let path = (0..p.log_n_parties() + p.m() - j - 1).map(|_| r.hash()).collect::<Result<_, _>>()?;
				ops.push(protocol::Opening { values, salt, path });
			}
			openings.push(ops);
		}
		if !r.0.is_empty() {
			return Err("trailing proof bytes".into());
		}
		Ok(Self {
			sc1,
			endpoints,
			sc2,
			value,
			pcs: PcsProof {
				roots,
				tail_root,
				xi,
				t,
				h_omega,
				coeffs,
				tails,
				tail_salts,
				openings,
			},
		})
	}
}

// Public-support sparse arithmetic. Missing children mean public structural zeros.
type Pair = [Option<usize>; 2];
pub(crate) fn sparse_pairs(indices: &[usize]) -> (Vec<usize>, Vec<Pair>) {
	// Pair physical siblings while retaining their positions in the caller's arrays.
	// Only a nonmonotone initial map needs sorting; later parent lists are sorted.
	let mut order = Vec::new();
	if !indices.windows(2).all(|p| p[0] < p[1]) {
		order = (0..indices.len()).collect::<Vec<_>>();
		order.sort_unstable_by_key(|&at| indices[at]);
	}
	let (mut parents, mut pairs) = (Vec::new(), Vec::<Pair>::new());
	for offset in 0..indices.len() {
		let at = if order.is_empty() { offset } else { order[offset] };
		let idx = indices[at];
		let parent = idx >> 1;
		if parents.last() != Some(&parent) {
			parents.push(parent);
			pairs.push([None, None]);
		}
		pairs.last_mut().unwrap()[idx & 1] = Some(at);
	}
	(parents, pairs)
}
pub(crate) fn children(v: &[L], p: &Pair) -> [L; 2] {
	p.map(|i| i.map_or(L::ZERO, |i| v[i]))
}
pub(crate) fn sparse_round(w: &[L], z: &[L], pairs: &[Pair]) -> [L; 3] {
	let mut s = [L::ZERO; 3];
	let om = omega();
	for p in pairs {
		let [a, b] = children(w, p);
		let [c, d] = children(z, p);
		s[0] += a * c;
		s[1] += b * d;
		s[2] += (a + mul_b(a + b, om)) * (c + mul_b(c + d, om));
	}
	s
}
pub(crate) fn sparse_fold(v: &[L], pairs: &[Pair], r: L) -> Vec<L> {
	pairs
		.iter()
		.map(|p| {
			let [a, b] = children(v, p);
			a + (a + b) * r
		})
		.collect()
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::field::chi;

	fn boolean_point(index: usize, len: usize) -> Vec<L> {
		(0..len).map(|i| if (index >> i) & 1 == 0 { L::ZERO } else { L::ONE }).collect()
	}

	// Directly contract the raw sparse rows. This does not call Base::weight or either
	// Config weight routine, and expands the full physical address equality table.
	fn raw_matrix_values(cfg: &Config, rcol: &[L], ry: &[L], rho: [L; 3], digests: &[[u8; 32]], point: &[L]) -> (L, L) {
		let base = &cfg.circuit.base;
		let ej = eq_expand(&rcol[..base.log_m0]);
		let eg = eq_expand(&rcol[base.log_m0..]);
		let ey = eq_expand(ry);
		let ep = eq_expand(point);
		let mut private = L::ZERO;
		let mut public = L::ZERO;
		for g in 0..cfg.groups {
			let mut digest_bits = vec![L::ONE; 257];
			for bit in 0..256 {
				digest_bits[1 + bit] = (0..cfg.ctx.k).filter(|&y| {
					let digest = &digests[g + cfg.groups * y];
					(digest[4 * (bit / 32) + 3 - (bit % 32) / 8] >> (bit % 8)) & 1 != 0
				}).map(|y| ey[y]).sum();
			}
			for (matrix, &r) in [&base.a, &base.b, &base.c].into_iter().zip(&rho) {
				for (j, row) in matrix.iter().enumerate() {
					let mut row_private = L::ZERO;
					let mut row_public = L::ZERO;
					for &p in row {
						if p < cfg.circuit.private_len {
							row_private += ep[cfg.map[g * base.n0() + p]];
						} else {
							row_public += digest_bits[p - cfg.circuit.private_len];
						}
					}
					private += eg[g] * ej[j] * r * row_private;
					public += eg[g] * ej[j] * r * row_public;
				}
			}
		}
		(private, public)
	}

	fn check_matrix_weights(cfg: &Config, rng: &mut StdRng) {
		let base = &cfg.circuit.base;
		let (mask_start, mask_row) = cfg.circuit.mask_start.unwrap();
		// Check the complete allocator invariant once in the test, not in each evaluation.
		for g in 0..cfg.groups {
			for p in (0..base.n0()).step_by(D) {
				let first = cfg.map[g * base.n0() + p];
				assert_eq!(first % D, 0);
				for h in 0..D { assert_eq!(cfg.map[g * base.n0() + p + h], first + h); }
				let x = first / D;
				assert!(!cfg.pcs.layout.is_pad[x]);
				assert!(cfg.pcs.layout.masks.iter().flatten().all(|m| m.x != x));
			}
			for block in 0..4 {
				let start = g * base.n0() + mask_start + 1024 * block;
                let columns:Vec<_>=(0..4).map(|j|cfg.map[start+j*D]/D).collect();
                let a=columns[0]^columns[1];let b=columns[0]^columns[2];
                assert!(a.is_power_of_two()&&b.is_power_of_two()&&a!=b);
                assert_eq!(columns[0]&(a|b),0);
                assert_eq!(columns[3],columns[0]^a^b);
                for h in 0..1024 {assert_eq!(cfg.map[start+h],columns[h/D]*D+h%D);}
			}
		}
		assert!(cfg.map.windows(2).any(|pair| pair[1] != pair[0] + 1));
		let digests: Vec<[u8; 32]> = (0..cfg.batch()).map(|_| {
			let mut d = [0; 32]; rng.fill_bytes(&mut d); d
		}).collect();
		for boolean in [false, true] {
			let row_len = base.log_m0 + cfg.groups.trailing_zeros() as usize;
			let rcol = if boolean { boolean_point(mask_row + 1024 + 7 + base.m0() * (cfg.groups - 1), row_len) }
				else { (0..row_len).map(|_| L::random(&mut *rng)).collect() };
			let ry = if boolean { boolean_point(cfg.ctx.k - 1, cfg.pcs.log_k()) }
				else { (0..cfg.pcs.log_k()).map(|_| L::random(&mut *rng)).collect() };
			let point = if boolean { boolean_point(cfg.map[base.n0() * (cfg.groups - 1) + mask_start + 1024 + 7], cfg.sc2_len()) }
				else { (0..cfg.sc2_len()).map(|_| L::random(&mut *rng)).collect() };
			let rho = std::array::from_fn(|_| L::random(&mut *rng));
			let weights = cfg.matrix_weights(&rcol, &ry, rho, &digests);
			let (indices, old, old_public) = cfg.weights(&rcol, &ry, rho, &digests);
			let old_value: L = indices.iter().zip(&old).map(|(&p, &w)| chi(p, &point) * w).sum();
			let (raw_value, raw_public) = raw_matrix_values(cfg, &rcol, &ry, rho, &digests, &point);
			assert_eq!(weights.evaluate(cfg, &point), old_value);
			assert_eq!(weights.evaluate(cfg, &point), raw_value);
			assert_eq!(weights.public, old_public);
			assert_eq!(weights.public, raw_public);
			let hole = boolean_point(cfg.pcs.layout.pad[0] * D, cfg.sc2_len());
			assert_eq!(weights.evaluate(cfg, &hole), L::ZERO);
		}
	}

    #[test]
    fn arbitrary_binary_rows_preserve_relation_under_cube_transport() {
        use rand::RngExt;
        let mut rng = StdRng::seed_from_u64(0x47454e45524943);
        for fanin in [1, 3, 11] {
            let mut circuit = ShaCircuit::synthetic_zk(48);
            // Replace the original constraints by unrelated binary row maps;
            // leave the four valid random blocks and public constant intact.
            for matrix in [&mut circuit.base.a, &mut circuit.base.b, &mut circuit.base.c] {
                for row in matrix.iter_mut().take(circuit.constraint_len - 3072) {
                    *row = (0..fanin).map(|_| rng.random_range(0..circuit.sha_private_len)).collect();
                    row.extend([0, 0]); // repeated entries cancel over F2
                }
            }
            let cfg = Config::from_circuit(16, 2, 16, 3, circuit);
            check_matrix_weights(&cfg, &mut rng);
            let n0 = cfg.circuit.base.n0();
            for group in 0..cfg.groups {
                let logical: Vec<bool> = (0..n0).map(|_| rng.random()).collect();
                let mut physical = vec![false; D * cfg.pcs.params.n()];
                for p in 0..n0 { physical[cfg.map[group*n0+p]] = logical[p]; }
                for matrix in [&cfg.circuit.base.a, &cfg.circuit.base.b, &cfg.circuit.base.c] {
                    for row in matrix {
                        let before = row.iter().filter(|&&p| p < cfg.circuit.private_len)
                            .fold(false, |v,&p| v ^ logical[p]);
                        let after = row.iter().filter(|&&p| p < cfg.circuit.private_len)
                            .fold(false, |v,&p| v ^ physical[cfg.map[group*n0+p]]);
                        assert_eq!(before, after);
                    }
                }
            }
        }
    }

    #[test]
    fn formal_sha_and_keccak_cubes_match_derived_geometry() {
        for (keccak,total,ell1,expected_ells) in [
            (false,64,23,[13,13,12,12]),
            (true,1024,26,[16,15,14,13]),
        ] {
            for (np,ell) in [32,64,128,256].into_iter().zip(expected_ells) {
                let groups=total/(np/4);
                let cfg=if keccak {crate::sha_zk::Config::new_keccak(np,groups,871,4)}
                    else {crate::sha_zk::Config::new(np,groups,871,4)};
                assert_eq!(cfg.pcs.params.ell,ell);
                assert_eq!(cfg.sc1_len(),ell1);
                assert_eq!(cfg.sc2_len(),8+ell);
                assert_eq!(cfg.g.params.ell,11);
                assert_eq!(cfg.gmap.len(),4*ell1+3*(8+ell));
                let mut seen=vec![false;cfg.pcs.params.n()];
                for chunk in cfg.map.chunks(D) {
                    let x=chunk[0]/D;
                    assert!(!seen[x]);seen[x]=true;
                    assert!(!cfg.pcs.layout.is_pad[x]);
                    assert!(cfg.pcs.layout.masks.iter().flatten().all(|m|m.x!=x));
                    for (h,&a) in chunk.iter().enumerate(){assert_eq!(a,x*D+h);}
                }
                let start=cfg.circuit.mask_start.unwrap().0;
                let mut common_axes=None;
                for group in 0..groups {for block in 0..4 {
                    let at=group*cfg.circuit.base.n0()+start+1024*block;
                    let cols:Vec<_>=(0..4).map(|j|cfg.map[at+j*D]/D).collect();
                    let axes=(cols[0]^cols[1],cols[0]^cols[2]);
                    assert!(axes.0.is_power_of_two()&&axes.1.is_power_of_two()&&axes.0!=axes.1);
                    assert_eq!(cols[0]&(axes.0|axes.1),0);
                    assert_eq!(cols[3],cols[0]^axes.0^axes.1);
                    if let Some(previous)=common_axes {assert_eq!(axes,previous);}else{common_axes=Some(axes);}
                }}
                println!("geometry keccak={keccak} N={np} ell={ell} ell1={ell1} ell2={} Gell=11 coefficients={}",8+ell,cfg.gmap.len());
            }
        }
    }

    #[test]
    fn global_capacity_other_axes_rank_and_raw_matrix_values() {
        let cfg=Config::new_zk(128,2,871,4);
        let mut rng=StdRng::seed_from_u64(0x43554245);
        check_matrix_weights(&cfg,&mut rng);
        let point:Vec<L>=(0..cfg.sc2_len()).map(|_|L::random(&mut rng)).collect();
        let start=cfg.circuit.mask_start.unwrap().0;
        for g in 0..cfg.groups {for block in 0..4 {
            let at=g*cfg.circuit.base.n0()+start+block*1024;
            let c:Vec<_>=(0..4).map(|i|cfg.map[at+i*D]/D).collect();
            let axes=[(c[0]^c[1]).trailing_zeros() as usize+8,(c[0]^c[2]).trailing_zeros() as usize+8];
            assert_ne!(axes,[8,9]);
            let selected:Vec<_>=(0..8).chain(axes).collect();
            let mut outside=L::ONE;
            for i in 0..point.len() {if !selected.contains(&i) {outside*=if (cfg.map[at]>>i)&1==1 {point[i]} else {L::ONE+point[i]};}}
            assert_ne!(outside,L::ZERO);
            let eq=eq_expand(&selected.iter().map(|&i|point[i]).collect::<Vec<_>>());
            let mut pivots=[[0u128;2];D];let mut rank=0;
            for j in 0..1024 {
                let physical=chi(cfg.map[at+j],&point);
                assert_eq!(physical,outside*eq[j]);
                let mut v=crate::field::to_words(physical);
                for i in (0..D).rev() {
                    if (v[i/128]>>(i%128))&1==0 {continue;}
                    if pivots[i]==[0,0] {pivots[i]=v;rank+=1;break;}
                    v[0]^=pivots[i][0];v[1]^=pivots[i][1];
                }
            }
            assert_eq!(rank,D);
        }}
    }

	#[test]
	fn global_capacity_sha64_main_and_g_dimensions() {
		for (n,ell) in [(32,13),(64,13),(128,12),(256,12)] {
			let cfg=crate::sha_zk::Config::new(n,256/n,871,4);
			assert_eq!(cfg.pcs.params.ell,ell,"main N={n}");
			assert_eq!(cfg.g.params.ell,11,"G N={n}");
			assert!(cfg.gmap.iter().any(|&cell|cell>=cfg.g.params.n()));
		}
	}

	#[test]
	fn mask_first_sha64_uses_8192_columns_at_n64() {
		for (n, ell) in [(32, 13), (64, 13), (128, 12), (256, 12)] {
			let cfg = Config::new_zk(n, 256 / n, 871, 4);
			assert_eq!(cfg.pcs.params.ell, ell, "N={n}");
			let mut seen = std::collections::HashSet::new();
			for &a in &cfg.map {
				assert!(seen.insert(a), "duplicate physical bit");
				assert!(!cfg.pcs.layout.is_pad[a / D]);
				assert!(cfg.pcs.layout.masks.iter().flatten().all(|m| m.x != a / D));
			}
			let start = cfg.circuit.mask_start.unwrap().0;
			for g in 0..cfg.groups { for b in 0..4 {
				let at = g * cfg.circuit.base.n0() + start + b * 1024;
                let c:Vec<_>=(0..4).map(|j|cfg.map[at+j*D]/D).collect();
                let a=c[0]^c[1];let b=c[0]^c[2];
                assert!(a.is_power_of_two()&&b.is_power_of_two()&&a!=b);
                assert_eq!(c[0]&(a|b),0);assert_eq!(c[3],c[0]^a^b);
                for j in 0..1024 {assert_eq!(cfg.map[at+j],c[j/D]*D+j%D);}
			}}
		}
	}

	#[test]
	fn nonmonotone_sparse_folds_match_dense_multilinear_evaluation() {
		let mut indices = vec![17, 30, 3, 8, 2, 31, 9, 1, 62, 45];
		let mut rng = StdRng::seed_from_u64(0x4d41534b);
		let mut values: Vec<L> = indices.iter().map(|_| L::random(&mut rng)).collect();
		let mut weights: Vec<L> = indices.iter().map(|_| L::random(&mut rng)).collect();
		let mut dense = vec![L::ZERO; 64]; let mut dw = dense.clone();
		for (at, &i) in indices.iter().enumerate() { dense[i] = values[at]; dw[i] = weights[at]; }
		for _ in 0..6 {
			let (parents, pairs) = sparse_pairs(&indices);
			let dp: Vec<_> = (0..dense.len()/2).map(|i| [Some(2*i), Some(2*i+1)]).collect();
			assert_eq!(sparse_round(&weights, &values, &pairs), sparse_round(&dw, &dense, &dp));
			let r = L::random(&mut rng);
			values = sparse_fold(&values, &pairs, r); weights = sparse_fold(&weights, &pairs, r);
			dense = fold_l(&dense, r); dw = fold_l(&dw, r);
			assert!(parents.windows(2).all(|p| p[0] < p[1]));
			for (at, &i) in parents.iter().enumerate() { assert_eq!(values[at], dense[i]); assert_eq!(weights[at], dw[i]); }
			indices = parents;
		}
		assert_eq!(values, dense); assert_eq!(weights, dw);
	}

	#[test]
	fn matrix_weights_packed_equivalence_and_mask_alignment() {
		let mut rng = StdRng::seed_from_u64(0x535452554354);
		for n in [8, 16, 32] {
			for groups in [1, 2, 4] {
				let mut circuit = ShaCircuit::synthetic_zk(48);
				// Repeated raw entries must cancel in characteristic two.
				circuit.base.a[0].extend([0, 0]);
				let cfg = Config::from_circuit(n, groups, 16, 3, circuit);
				check_matrix_weights(&cfg, &mut rng);
			}
		}
	}

	#[test]
	fn matrix_weights_real_sha_equivalence() {
		let cfg = Config::new_zk(16, 2, 16, 3);
		assert_eq!(cfg.circuit.private_len, 113664);
		check_matrix_weights(&cfg, &mut StdRng::seed_from_u64(0x534841323536));
	}

	#[test]
	fn matrix_weights_match_actual_index() {
		let mut cfg = crate::sha_zk::Config::synthetic(8, 2, 16, 3, 48);
		let public_bit = cfg.circuit.private_len + 1;
		assert!(!cfg.circuit.base.a[0].contains(&0));
		assert!(!cfg.circuit.base.a[0].contains(&public_bit));
		cfg.inner.circuit.base.a[0].extend([0, 0, public_bit, public_bit]);
		let index = crate::indexed::Index::new(&cfg, 16);
		for g in 0..cfg.groups {
			let row = g * cfg.circuit.base.m0();
			assert!(!index.private.entries.contains(&(0, row, cfg.map[g * cfg.circuit.base.n0()])));
			assert!(!index.public.entries.contains(&(0, row, g * 512 + 1)));
		}
		assert!(cfg.map.windows(2).any(|pair| pair[1] != pair[0] + 1));
		let mask_address = cfg.pcs.layout.masks[0][0].x * D;
		assert!(!cfg.map.contains(&mask_address));
		let mut rng = StdRng::seed_from_u64(0x494e444558);
		let digests: Vec<[u8; 32]> = (0..cfg.batch()).map(|_| {
			let mut d = [0; 32]; rng.fill_bytes(&mut d); d
		}).collect();
		for boolean in [false, true] {
			let row_len = cfg.circuit.base.log_m0 + cfg.groups.trailing_zeros() as usize;
			let rcol = if boolean { boolean_point(cfg.circuit.base.m0(), row_len) }
				else { (0..row_len).map(|_| L::random(&mut rng)).collect() };
			let ry: Vec<_> = (0..cfg.pcs.log_k()).map(|_| L::random(&mut rng)).collect();
			let point: Vec<_> = (0..cfg.sc2_len()).map(|_| L::random(&mut rng)).collect();
			let rho = std::array::from_fn(|_| L::random(&mut rng));
			let weights = cfg.matrix_weights(&rcol, &ry, rho, &digests);
			assert_eq!(weights.evaluate(&cfg, &point), index.private.evaluate(&rcol, &point, rho));
			let public_inputs = crate::indexed::public_vector(cfg.groups, cfg.ctx.k, &ry, &digests, cfg.circuit.keccak);
			let public: L = index.public.column_weights(&rcol, rho).iter().zip(&public_inputs)
				.map(|(&w, &input)| w * input).sum();
			assert_eq!(weights.public, public);
			let hole = boolean_point(mask_address, cfg.sc2_len());
			assert_eq!(index.private.evaluate(&rcol, &hole, rho), L::ZERO);
			assert_eq!(weights.evaluate(&cfg, &hole), L::ZERO);
		}
	}

	#[test]
	fn sparse_rounds_equal_dense_zero_padding() {
		let mut rng = StdRng::seed_from_u64(92);
		let mut indices = vec![1, 2, 3, 8, 9, 17, 30, 31, 45, 62];
		let mut w: Vec<L> = indices.iter().map(|_| L::random(&mut rng)).collect();
		let mut z: Vec<L> = indices.iter().map(|_| L::random(&mut rng)).collect();
		let (mut dw, mut dz) = (vec![L::ZERO; 64], vec![L::ZERO; 64]);
		for (a, &i) in indices.iter().enumerate() {
			dw[i] = w[a];
			dz[i] = z[a];
		}
		for _ in 0..6 {
			let (parents, pairs) = sparse_pairs(&indices);
			let dense_pairs: Vec<_> = (0..dw.len() / 2).map(|i| [Some(2 * i), Some(2 * i + 1)]).collect();
			assert_eq!(sparse_round(&w, &z, &pairs), sparse_round(&dw, &dz, &dense_pairs));
			let r = L::random(&mut rng);
			w = sparse_fold(&w, &pairs, r);
			z = sparse_fold(&z, &pairs, r);
			dw = fold_l(&dw, r);
			dz = fold_l(&dz, r);
			indices = parents;
			for (a, &i) in indices.iter().enumerate() {
				assert_eq!(w[a], dw[i]);
				assert_eq!(z[a], dz[i]);
			}
		}
		assert_eq!(indices, vec![0]);
		assert_eq!(w, dw);
		assert_eq!(z, dz);
	}

	#[test]
	fn sha_spartan_pcs_roundtrip_and_mutations() {
		let cfg = Config::new(8, 1, 16, 3);
		let run = prove(&cfg, 1234);
		let encoded = run.proof.to_bytes();
		let proof = Proof::from_bytes(&cfg, &encoded).unwrap();
		assert!(verify(&cfg, &run.digests, &proof).is_ok());
		let mut d = run.digests.clone();
		d[0][0] ^= 1;
		assert!(verify(&cfg, &d, &proof).is_err());
		let mut bad = proof.clone();
		bad.sc1[0][0] += L::ONE;
		assert!(verify(&cfg, &run.digests, &bad).is_err());
		let mut bad = proof.clone();
		bad.sc2[0][1] += L::ONE;
		assert!(verify(&cfg, &run.digests, &bad).is_err());
		let mut bad = proof.clone();
		bad.value += L::ONE;
		assert!(verify(&cfg, &run.digests, &bad).is_err());
		let mut bad = proof.clone();
		bad.endpoints[1] += L::ONE;
		assert!(verify(&cfg, &run.digests, &bad).is_err());
		let mut bad = proof.clone();
		bad.pcs.roots[0][0] ^= 1;
		assert!(verify(&cfg, &run.digests, &bad).is_err());
		let mut bad = proof.clone();
		bad.pcs.tails[0][0] += L::ONE;
		assert!(verify(&cfg, &run.digests, &bad).is_err());
		assert!(Proof::from_bytes(&cfg, &encoded[..encoded.len() - 1]).is_err());
		let mut bad = encoded;
		bad.push(0);
		assert!(Proof::from_bytes(&cfg, &bad).is_err());
	}
}

/// Matched ideal-functionality payload categories for the legacy non-ZK baseline.
pub fn communication(cfg:&Config,p:&Proof)->(usize,usize,usize,usize){
 let n=cfg.ctx.n;
 let client=n*cfg.groups*(cfg.circuit.private_len+3*cfg.circuit.base.m0())*16+n*(cfg.pcs.params.n()-cfg.pcs.layout.pad.len())*32;
 let preprocessing=n*(cfg.pcs.layout.pad.len()+2*(1+cfg.ctx.k))*32;
 let mut aggregate=n*32*(4*cfg.sc1_len()+3*cfg.sc2_len()+3+1+2);
 let s=&p.pcs;
 aggregate+=n*32*(s.roots.len()+2*s.coeffs.len()+2+crate::field::D+1);
 aggregate+=s.tails.iter().map(|v|v.len()*32+32).sum::<usize>();
 aggregate+=s.openings.iter().flatten().map(|o|96+32*(o.path.len()-cfg.pcs.params.log_n_parties())).sum::<usize>();
 (client,preprocessing,aggregate,p.to_bytes().len()+2*cfg.ctx.k*32)
}
