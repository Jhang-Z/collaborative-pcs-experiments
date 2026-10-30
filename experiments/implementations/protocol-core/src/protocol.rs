//! The collaborative opening protocol (Section 4, Figure 2) with the non-interactive format of
//! Section 4.9, executed in one process: every party's computation runs in its own [`Party`]
//! value and is timed separately; aggregation and Fiat–Shamir are done by the coordinator.

use std::time::{Duration, Instant};

use binius_hash::HashSuite;
use rand::{Rng, RngExt, SeedableRng, rngs::StdRng};

use crate::{
	algebra::{LinearMap, Tensor, bits_of, chi_map},
	code::fold_coeffs,
	field::{D, Field, L, basis, chi, eq_expand, to_words},
	fs::Transcript,
	merkle::{Hash, Hasher, Tree, multiproof_size, root_from_path},
	setup::{Instance, Setup, Witness},
};

pub(crate) const TAG_TAIL: u64 = 1 << 32;

pub(crate) fn l_bytes(v: &[L]) -> &[u8] {
	bytemuck::cast_slice(v)
}

pub(crate) fn dummy_root<H: HashSuite>(h: &Hasher<H>, round:u64) -> Hash {
    // Global application roles keep their measured encoding. Standalone PCS uses
    // three independent one-leaf oracle domains for its non-oracle-only rounds.
    if h.standalone() {h.at_layer((1u64<<63)|round).leaf(u64::MAX,0,&[0],&[])}
    else {h.leaf(u64::MAX, 0, &[0], &[])}
}

/// Per-party timings, by phase.
#[derive(Clone, Debug, Default)]
pub struct Timings {
	pub share: Duration,
	pub encode: Duration,
	pub hash: Duration,
	pub frontend: Duration,
	pub weights: Duration,
	pub rounds: Duration,
}

impl Timings {
	pub fn total(&self) -> Duration {
		self.share + self.encode + self.hash + self.frontend + self.weights + self.rounds
	}
}

/// One party's state.
pub struct Party {
	pub id: usize,
	/// Current (folded) share-row X'_i^{(j)}.
	pub(crate) row: Vec<L>,
	/// Current (folded) share-row weight W'_i^{(j)}.
	pub(crate) weight: Vec<L>,
	/// Committed codewords f_j(i, ·), j < ℓ - τ.
	pub(crate) codewords: Vec<Vec<L>>,
	pub(crate) salts: Vec<Vec<[u8; 32]>>,
	pub(crate) subtrees: Vec<Tree>,
	pub(crate) tail_salt: [u8; 32],
	/// χ_x(r_B) for all columns (shared by the frontend and the weights).
	pub(crate) eb: Vec<L>,
	pub(crate) rng: StdRng,
	/// Optional fresh per-proof salt material generated before the online barrier.
	pub(crate) prepared_salts: Vec<Vec<[u8; 32]>>,
	pub time: Timings,
}

/// One opened fibre.
#[derive(Clone)]
pub struct Opening {
	pub values: [L; 2],
	pub salt: [u8; 32],
	pub path: Vec<Hash>,
}

#[derive(Clone)]
pub struct Proof {
	pub roots: Vec<Hash>,
	pub tail_root: Hash,
	pub xi: L,
	pub t: Vec<L>,
	pub h_omega: L,
	pub coeffs: Vec<(L, L)>,
	pub tails: Vec<Vec<L>>,
	pub tail_salts: Vec<[u8; 32]>,
	/// openings[a][j]: query a, layer j.
	pub openings: Vec<Vec<Opening>>,
}

/// Bytes of a compact serialization: field elements and salts at 32 bytes, Merkle siblings
/// deduplicated per tree, roots included.
#[derive(Clone, Debug, Default)]
pub struct ProofSize {
	pub queries: usize,
	pub tails: usize,
	pub frontend: usize,
	pub total: usize,
}

pub(crate) struct Challenges {
	pub(crate) alpha: L,
	pub(crate) r_pp: Vec<L>,
	pub(crate) omega: Vec<L>,
	pub(crate) eps: L,
	pub(crate) r: Vec<L>,
}

impl Party {
	pub(crate) fn new(id: usize, n: usize, seed: u64) -> Self {
		Self {
			id,
			row: vec![L::ZERO; n],
			weight: Vec::new(),
			codewords: Vec::new(),
			salts: Vec::new(),
			subtrees: Vec::new(),
			tail_salt: [0; 32],
			eb: Vec::new(),
			rng: StdRng::seed_from_u64(seed),
			prepared_salts: Vec::new(),
			time: Timings::default(),
		}
	}

	pub(crate) fn prepare_salts(&mut self, setup: &Setup) {
		assert!(self.codewords.is_empty() && self.prepared_salts.is_empty());
		self.prepared_salts = (0..setup.params.folds()).map(|j| {
			let mut salts=vec![[0u8;32];setup.params.fibres(j)];
			for s in &mut salts {self.rng.fill_bytes(s);}
			salts
		}).collect();
		self.rng.fill_bytes(&mut self.tail_salt);
	}

	/// Encodes layer j's codeword and builds this party's Merkle subtree for it.
	pub(crate) fn commit_layer<H: HashSuite>(&mut self, setup: &Setup, hasher: &Hasher<H>, j: usize, cw: Vec<L>) {
		let t0 = Instant::now();
  let lh=hasher.at_layer(j as u64);let hasher=&lh;
		let fib = cw.len() / 2;
		let salts = if self.prepared_salts.is_empty() {
			let mut salts=vec![[0u8;32];fib];
			for s in &mut salts {self.rng.fill_bytes(s);}
			salts
		} else {let salts=std::mem::take(&mut self.prepared_salts[j]);assert_eq!(salts.len(),fib);salts};
		let base = (self.id * fib) as u64;
		let leaves: Vec<Hash> = (0..fib)
			.map(|q| hasher.leaf(j as u64, base + q as u64, l_bytes(&cw[2 * q..2 * q + 2]), &salts[q]))
			.collect();
		self.subtrees.push(Tree::build(hasher, leaves));
		self.salts.push(salts);
		self.codewords.push(cw);
		let _ = setup;
		self.time.hash += t0.elapsed();
	}

	/// ξ_i and T_i of server i, from its share-row alone (Section 4.5): with the reconstruction
	/// coefficients Λ_{i,y}, X(y, x) = Σ_i Λ_{i,y} X'_i(x) for every non-padding column x, so
	/// ξ = Σ_i ξ_i and T = Σ_i T_i.
	///   ξ_i     = Σ_θ β_{h_θ} ψ(Λ_{i,y_θ} X'_i(x_θ)),
	///   T_{i,u} = Σ_{y,v} Λ_{i,y} [a_y β_v]_u Z_v + Σ_θ Λ_{i,y_θ} X'_i(x_θ) ([h_θ = u] - [a_{y_θ} b_{x_θ}]_u),
	/// with a_y = α χ_y(r_A), b_x = χ_x(r_B) and Z_v = Σ_{x ∉ Pad} [b_x]_v X'_i(x).
	pub(crate) fn frontend(&mut self, setup: &Setup, inst: &Instance, alpha: Option<L>) -> Vec<L> {
		let t0 = Instant::now();
		let n = setup.params.n();
		let lay = &setup.layout;
		let lam = &setup.lagrange[self.id];
		let active = lam.iter().any(|&l| l != L::ZERO);
		let out = match alpha {
			None => {
				let mut xi = L::ZERO;
				if active {
					let psi = chi_map(&inst.r_h);
					for m in lay.masks.iter().flatten() {
						xi += basis(m.h) * psi.apply(lam[m.y] * self.row[m.x]);
					}
				}
				vec![xi]
			}
			Some(alpha) => {
				let mut t = vec![L::ZERO; D];
				if active {
					if self.eb.is_empty() {
						self.eb = eq_expand(&inst.r_b);
					}
					// Z_v: accumulate each column into one bucket per byte of b_x, then expand the
					// buckets bit by bit (32 additions per column instead of one per set bit).
					let mut buckets = vec![[L::ZERO; 256]; D / 8];
					for x in 0..n {
						if lay.is_pad[x] {
							continue;
						}
						let bytes: [u8; 32] = bytemuck::cast(to_words(self.eb[x]));
						let v = self.row[x];
						for (bk, &b) in buckets.iter_mut().zip(&bytes) {
							bk[b as usize] += v;
						}
					}
					let mut z = vec![L::ZERO; D];
					for (p, bk) in buckets.iter().enumerate() {
						for (b, &s) in bk.iter().enumerate().skip(1) {
							for j in 0..8 {
								if (b >> j) & 1 == 1 {
									z[8 * p + j] += s;
								}
							}
						}
					}
					// Σ_{y,v} Λ_{i,y} [a_y β_v]_u Z_v.
					let ay: Vec<L> = eq_expand(&inst.r_a).iter().map(|&e| alpha * e).collect();
					for (y, &l) in lam.iter().enumerate() {
						if l == L::ZERO {
							continue;
						}
						for (v, &zv) in z.iter().enumerate() {
							let lz = l * zv;
                            // Enumerate public set coordinates directly, as Tensor does.
                            for (half, mut word) in to_words(ay[y] * basis(v)).into_iter().enumerate() {
                                while word != 0 {
                                    let u=128*half+word.trailing_zeros() as usize;
                                    t[u]+=lz;
                                    word &= word-1;
                                }
                            }
						}
					}
					// Tensor masks: their entries count at h_θ instead of as data.
					for m in lay.masks.iter().flatten() {
						let val = lam[m.y] * self.row[m.x];
						t[m.h] += val;
						for u in bits_of(ay[m.y] * self.eb[m.x]) {
							t[u] += val;
						}
					}
				}
				t
			}
		};
		self.time.frontend += t0.elapsed();
		out
	}

	#[cfg(test)]
	pub(crate) fn frontend_reference(&mut self, setup: &Setup, inst: &Instance, alpha: Option<L>) -> Vec<L> {
		let t0 = Instant::now();
		let n = setup.params.n();
		let lay = &setup.layout;
		let lam = &setup.lagrange[self.id];
		let active = lam.iter().any(|&l| l != L::ZERO);
		let out = match alpha {
			None => {
				let mut xi = L::ZERO;
				if active {
					let psi = chi_map(&inst.r_h);
					for m in lay.masks.iter().flatten() {
						xi += basis(m.h) * psi.apply(lam[m.y] * self.row[m.x]);
					}
				}
				vec![xi]
			}
			Some(alpha) => {
				let mut t = vec![L::ZERO; D];
				if active {
					if self.eb.is_empty() {
						self.eb = eq_expand(&inst.r_b);
					}
					// Z_v: accumulate each column into one bucket per byte of b_x, then expand the
					// buckets bit by bit (32 additions per column instead of one per set bit).
					let mut buckets = vec![[L::ZERO; 256]; D / 8];
					for x in 0..n {
						if lay.is_pad[x] {
							continue;
						}
						let bytes: [u8; 32] = bytemuck::cast(to_words(self.eb[x]));
						let v = self.row[x];
						for (bk, &b) in buckets.iter_mut().zip(&bytes) {
							bk[b as usize] += v;
						}
					}
					let mut z = vec![L::ZERO; D];
					for (p, bk) in buckets.iter().enumerate() {
						for (b, &s) in bk.iter().enumerate().skip(1) {
							for j in 0..8 {
								if (b >> j) & 1 == 1 {
									z[8 * p + j] += s;
								}
							}
						}
					}
					// Σ_{y,v} Λ_{i,y} [a_y β_v]_u Z_v.
					let ay: Vec<L> = eq_expand(&inst.r_a).iter().map(|&e| alpha * e).collect();
					for (y, &l) in lam.iter().enumerate() {
						if l == L::ZERO {
							continue;
						}
						for (v, &zv) in z.iter().enumerate() {
							let lz = l * zv;
							for u in bits_of(ay[y] * basis(v)) {
								t[u] += lz;
							}
						}
					}
					// Tensor masks: their entries count at h_θ instead of as data.
					for m in lay.masks.iter().flatten() {
						let val = lam[m.y] * self.row[m.x];
						t[m.h] += val;
						for u in bits_of(ay[m.y] * self.eb[m.x]) {
							t[u] += val;
						}
					}
				}
				t
			}
		};
		self.time.frontend += t0.elapsed();
		out
	}

	/// ξ_p and T_p of an owner from its plaintext columns (the pre-delegation form; kept to check
	/// that the share-based sums agree).
	#[cfg(test)]
	pub(crate) fn frontend_owner(&mut self, setup: &Setup, w: &Witness, inst: &Instance, alpha: Option<L>) -> Vec<L> {
		let t0 = Instant::now();
		let (n, k) = (setup.params.n(), setup.params.k());
		let lay = &setup.layout;
		let masks = &lay.masks[self.id];
		let out = match alpha {
			None => {
				// ξ_p = Σ_θ β_{h_θ} ψ(X(θ)).
				let psi = chi_map(&inst.r_h);
				vec![masks.iter().map(|m| basis(m.h) * psi.apply(w.get(n, m.y, m.x))).sum()]
			}
			Some(alpha) => {
				// T_{p,u} = Σ_data [α e_{y,x}]_u X(y,x) + X(θ_u).
				if self.eb.is_empty() {
					self.eb = eq_expand(&inst.r_b);
				}
				let ea = eq_expand(&inst.r_a);
				let ay: Vec<L> = ea.iter().map(|&e| alpha * e).collect();
				let mut t = vec![L::ZERO; D];
				for &x in &lay.owned[self.id] {
					for y in 0..k {
						let v = w.get(n, y, x);
						if let Some(h) = lay.mask_index(self.id, y, x) {
							t[h] += v;
							continue;
						}
						for u in bits_of(ay[y] * self.eb[x]) {
							t[u] += v;
						}
					}
				}
				t
			}
		};
		self.time.frontend += t0.elapsed();
		out
	}

	/// This party's contribution to H_ω = ⟨M_ω, X(0, ·)⟩.
	pub(crate) fn h_omega(&mut self, setup: &Setup, mask_w: &[(usize, L)]) -> L {
		let lam0 = setup.lagrange[self.id][0];
		lam0 * mask_w.iter().map(|&(x, m)| m * self.row[x]).sum::<L>()
	}

	/// The share-row weight W'_i (Section 4.8 and Appendix A).
	pub(crate) fn weights(&mut self, setup: &Setup, inst: &Instance, ch: &Challenges, mask_w: &[(usize, L)]) {
		let t0 = Instant::now();
		let (n, k) = (setup.params.n(), setup.params.k());
		let lam = &setup.lagrange[self.id];
		let mut wv = vec![L::ZERO; n];
		if lam.iter().any(|&l| l != L::ZERO) {
			if self.eb.is_empty() {
				self.eb = eq_expand(&inst.r_b);
			}
			let phi = chi_map(&ch.r_pp);
			let chi_pp = eq_expand(&ch.r_pp);
			let ay: Vec<L> = eq_expand(&inst.r_a).iter().map(|&e| ch.alpha * e).collect();
			// C_{i,u} = Σ_y Λ_{i,y} φ(a_y β_u).
			let c: Vec<L> = (0..D)
				.map(|u| (0..k).map(|y| lam[y] * phi.apply(ay[y] * basis(u))).sum())
				.collect();
			let cmap = LinearMap::new(&c);
			for x in 0..n {
				if !setup.layout.is_pad[x] {
					wv[x] = cmap.apply(self.eb[x]);
				}
			}
			// Tensor-mask corrections: replace the data contribution of each θ.
			for masks in &setup.layout.masks {
				for m in masks {
					let g = phi.apply(ay[m.y] * self.eb[m.x]);
					wv[m.x] += lam[m.y] * (chi_pp[m.h] - g);
				}
			}
			for &(x, mw) in mask_w {
				wv[x] += lam[0] * ch.eps * mw;
			}
		}
		self.weight = wv;
		self.time.weights += t0.elapsed();
	}

	/// Round polynomial coefficients (g_{i,j,0}, g_{i,j,2}).
	pub(crate) fn round_poly(&mut self) -> (L, L) {
		let t0 = Instant::now();
		let (mut g0, mut g2) = (L::ZERO, L::ZERO);
		for (w, x) in self.weight.chunks_exact(2).zip(self.row.chunks_exact(2)) {
			g0 += w[0] * x[0];
			g2 += (w[1] - w[0]) * (x[1] - x[0]);
		}
		self.time.rounds += t0.elapsed();
		(g0, g2)
	}

	/// Folds the share-row, the weight, and (if another layer is committed) the codeword.
	pub(crate) fn fold<H: HashSuite>(&mut self, setup: &Setup, hasher: &Hasher<H>, j: usize, r: L) {
		let t0 = Instant::now();
		self.row = fold_coeffs(&self.row, r);
		self.weight = fold_coeffs(&self.weight, r);
		let next = (j + 1 < setup.params.folds()).then(|| setup.row.fold(self.codewords.last().unwrap(), r));
		self.time.rounds += t0.elapsed();
		if let Some(cw) = next {
			self.commit_layer(setup, hasher, j + 1, cw);
		}
	}
}

/// Committed server state, consumed by exactly one opening. No plaintext witness remains.
pub struct Prepared {
    pub root: Hash,
    pub preprocessing: Duration,
    pub client_share: Duration,
    pub(crate) parties: Vec<Party>,
    pub(crate) role: u64,
}

/// Client sharing and server commitment, before the upper protocol's challenges.
pub fn prepare<H: HashSuite>(setup: &Setup, wit: &Witness, seed: u64) -> Prepared {
	let p = &setup.params;
	let (n, k, np) = (p.n(), p.k(), p.n_parties);
	let hasher = Hasher::<H>::default();
	let mut dealer = StdRng::seed_from_u64(seed ^ 0x5eed);
	let mut parties: Vec<Party> = (0..np).map(|i| Party::new(i, n, seed.wrapping_add(i as u64 + 1))).collect();

	// Per-proof F_rand padding, measured separately.
	let preprocessing_start = Instant::now();
	for &x in &setup.layout.pad {
		let shares = setup.sharing.random_shares(&mut dealer);
		for (i, s) in shares.into_iter().enumerate() {
			parties[i].row[x] = s;
		}
	}
	let preprocessing = preprocessing_start.elapsed();
	// Sharing: the client shares every non-padding column and leaves.
	let t0 = Instant::now();
	let mut rng = StdRng::seed_from_u64(seed ^ 0xc11e);
	for x in (0..n).filter(|&x| !setup.layout.is_pad[x]) {
		let vals: Vec<L> = (0..k).map(|y| wit.get(n, y, x)).collect();
		for (i, s) in setup.sharing.share(&vals, &mut rng).into_iter().enumerate() {
			parties[i].row[x] = s;
		}
	}
	let client_share = t0.elapsed();
	// Commitment: encode and hash layer 0.
	for party in &mut parties {
		let t0 = Instant::now();
		let cw = setup.row.encode(&party.row);
		party.time.encode += t0.elapsed();
		party.commit_layer(setup, &hasher, 0, cw);
	}
	let global_root = |parties: &[Party], j: usize| {
		Tree::build(&hasher.at_layer(j as u64), parties.iter().map(|q| q.subtrees[j].root()).collect()).root()
	};
	let root = global_root(&parties, 0);
	Prepared { parties, root, preprocessing, client_share, role:0 }
}


/// Full-entropy v0.4 sharing, independent per-party salt streams and role-scoped trees.
pub fn prepare_random<H:HashSuite>(setup:&Setup,wit:&Witness,rng:&mut impl Rng,role:u64)->Prepared {
	let p = &setup.params;
	let (n, k, np) = (p.n(), p.k(), p.n_parties);
	let hasher = Hasher::<H>::scoped(role);
 let mut dealer=StdRng::from_seed(rng.random());
 let mut parties:Vec<Party>=(0..np).map(|i|{let mut p=Party::new(i,n,0);p.rng=StdRng::from_seed(rng.random());p}).collect();

	// Per-proof F_rand padding, measured separately.
	let preprocessing_start = Instant::now();
	for &x in &setup.layout.pad {
		let shares = setup.sharing.random_shares(&mut dealer);
		for (i, s) in shares.into_iter().enumerate() {
			parties[i].row[x] = s;
		}
	}
	let preprocessing = preprocessing_start.elapsed();
	// Sharing: the client shares every non-padding column and leaves.
	let t0 = Instant::now();
	let mut rng = StdRng::from_seed(rng.random());
	for x in (0..n).filter(|&x| !setup.layout.is_pad[x]) {
		let vals: Vec<L> = (0..k).map(|y| wit.get(n, y, x)).collect();
		for (i, s) in setup.sharing.share(&vals, &mut rng).into_iter().enumerate() {
			parties[i].row[x] = s;
		}
	}
    if crate::transport::enabled(){let received=crate::transport::values(parties.iter().map(|p|p.row.clone()).collect(),false);for(p,v)in parties.iter_mut().zip(received){p.row=v;}}
	let client_share = t0.elapsed();
	// Commitment: encode and hash layer 0.
    crate::parallel::parties(&mut parties, |_,party| {
        let t0=Instant::now();let cw=setup.row.encode(&party.row);
        party.time.encode+=t0.elapsed();party.commit_layer(setup,&Hasher::<H>::scoped(role),0,cw);
    });
	let global_root = |parties: &[Party], j: usize| {
		Tree::build(&hasher.at_layer(j as u64), crate::transport::hashes(parties.iter().map(|q| q.subtrees[j].root()).collect())).root()
	};
	let root = global_root(&parties, 0);
	Prepared { parties, root, preprocessing, client_share, role }
}


/// Deterministic development/measurement entry point, with only a 64-bit seed.
/// Privacy with cryptographic coins requires independently seeded `prepare_random`.
pub fn prove<H: HashSuite>(setup: &Setup, inst: &Instance, wit: &Witness, seed: u64) -> (Proof, Vec<Timings>, Duration) {
    open_prepared::<H>(setup, inst, prepare::<H>(setup, wit, seed), &[])
}

pub(crate) fn bound_instance(setup:&Setup, inst: &Instance, context: &[u8]) -> Vec<u8> {
    let mut bytes=b"b2pcs-bound-opening-v4".to_vec();
    let p=&setup.params;
    for x in [p.n_parties,p.ell,p.beta,p.gamma,p.tau,p.salt_bytes] {bytes.extend_from_slice(&(x as u64).to_le_bytes());}
    bytes.extend_from_slice(&(context.len() as u64).to_le_bytes());
    bytes.extend_from_slice(context);
    bytes.extend_from_slice(&inst.to_bytes());
    bytes
}

/// Opens a precommitted state, bound to an upper protocol transcript.
pub fn open_prepared<H: HashSuite>(setup: &Setup, inst: &Instance, prepared: Prepared, context: &[u8]) -> (Proof, Vec<Timings>, Duration) {
 let hasher=Hasher::<H>::scoped(prepared.role);
 let mut tr=Transcript::new(&hasher,&bound_instance(setup,inst,context));
 open_prepared_in(setup,inst,prepared,&mut tr)
}
pub fn open_prepared_in<H:HashSuite>(setup:&Setup,inst:&Instance,prepared:Prepared,tr:&mut Transcript<'_,H>)->(Proof,Vec<Timings>,Duration) {
 let p=&setup.params;let np=p.n_parties;
 let hasher=Hasher::<H>::scoped(prepared.role);
 let Prepared { mut parties, root, client_share, role, .. }=prepared;
    let global_root = |parties: &[Party], j: usize| {
        Tree::build(&hasher.at_layer(j as u64), crate::transport::hashes(parties.iter().map(|q| q.subtrees[j].root()).collect())).root()
    };
    let mut roots=vec![root];
	let dummy2 = dummy_root(&hasher,2);
	let dummy3 = dummy_root(&hasher,3);
	let dummy4 = dummy_root(&hasher,4);

	// Round 1: ξ, then α.
	let xi: L = crate::transport::scalars(crate::parallel::parties(&mut parties, |_,q| q.frontend(setup, inst, None)[0])).into_iter().sum();
	let alpha = tr.round(&roots[0], l_bytes(&[xi])).field();
	// Round 2: T, then r'' and ω.
	let mut t = vec![L::ZERO; D];
    let partials=crate::parallel::parties(&mut parties, |_,q| q.frontend(setup,inst,Some(alpha)));
	for v in crate::transport::values(partials,true) {
		for (a, b) in t.iter_mut().zip(v) {
			*a += b;
		}
	}
	let mut c2 = tr.round(&dummy2, l_bytes(&t));
	let r_pp: Vec<L> = (0..crate::field::LOG_D).map(|_| c2.field()).collect();
	let omega: Vec<L> = (0..setup.n_omega()).map(|_| c2.field()).collect();
	// Round 3: H_ω, then ε.
	let mask_w = setup.mask_weight(&omega);
	let h_omega: L = crate::transport::scalars(crate::parallel::parties(&mut parties, |_,q| q.h_omega(setup, &mask_w))).into_iter().sum();
	let eps = tr.round(&dummy3, l_bytes(&[h_omega])).field();
	let mut ch = Challenges { alpha, r_pp, omega, eps, r: Vec::new() };
    crate::parallel::parties(&mut parties, |_,q| q.weights(setup,inst,&ch,&mask_w));
	// Folding rounds: round 4 + j absorbs layer j's root (dummy for j = 0) and (g_{j,0}, g_{j,2}).
	let mut coeffs = Vec::new();
	for j in 0..p.folds() {
		let (mut g0, mut g2) = (L::ZERO, L::ZERO);
        let partials=crate::parallel::parties(&mut parties, |_,q| q.round_poly());
		for [a,b] in crate::transport::arrays(partials.into_iter().map(|(a,b)|[a,b]).collect()) {
			g0 += a;
			g2 += b;
		}
		coeffs.push((g0, g2));
		let root = if j == 0 { dummy4 } else { roots[j] };
		let rj = tr.round(&root, l_bytes(&[g0, g2])).field();
		ch.r.push(rj);
        crate::parallel::parties(&mut parties, |_,q| q.fold(setup,&Hasher::<H>::scoped(role),j,rj));
		if j + 1 < p.folds() {
			roots.push(global_root(&parties, j + 1));
		}
	}
	// Termination: commit the tails, then sample the queries.
	let mut tail_salts = Vec::with_capacity(np);
	let mut tail_leaves = Vec::with_capacity(np);
	for q in parties.iter_mut() {
		let t0 = Instant::now();
		let mut salt = [0u8; 32];
		q.rng.fill_bytes(&mut salt);
		q.tail_salt = salt;
		tail_leaves.push(hasher.at_layer(TAG_TAIL).leaf(TAG_TAIL, q.id as u64, l_bytes(&q.row), &salt));
		tail_salts.push(salt);
		q.time.hash += t0.elapsed();
	}
	let tail_root = Tree::build(&hasher.at_layer(TAG_TAIL), crate::transport::hashes(tail_leaves)).root();
	let queries = sample_queries(setup, tr, &tail_root);
	let tops: Vec<Tree> = (0..p.folds())
		.map(|j| Tree::build(&hasher.at_layer(j as u64), parties.iter().map(|q| q.subtrees[j].root()).collect()))
		.collect();
	let openings = queries
		.iter()
		.map(|&(xa, qa)| {
			(0..p.folds())
				.map(|j| {
					let qj = qa >> j;
					let party = &parties[xa];
					let mut path = party.subtrees[j].path(qj);
					path.extend(tops[j].path(xa));
					Opening {
						values: [party.codewords[j][2 * qj], party.codewords[j][2 * qj + 1]],
						salt: party.salts[j][qj],
						path,
					}
				})
				.collect()
		})
		.collect();
	let openings=crate::transport::openings(openings,&queries,np);
    let tails=crate::transport::values(parties.iter().map(|q|q.row.clone()).collect(),true);
    let tail_salts=crate::transport::hashes(tail_salts);
	let times = parties.iter().map(|q| q.time.clone()).collect();
	let _ = (ch.omega.len(), &ch.eps);
	(
		Proof { roots, tail_root, xi, t, h_omega, coeffs, tails, tail_salts, openings },
		times,
		client_share,
	)
}

pub(crate) fn sample_queries<H: HashSuite>(setup: &Setup, tr: &mut Transcript<'_, H>, tail_root: &Hash) -> Vec<(usize, usize)> {
	let p = &setup.params;
	let mut c = tr.round(tail_root, &[]);
	let (row_bits, fib_bits) = (p.log_n_parties() as u32, (p.m() - 1) as u32);
	(0..p.gamma)
		.map(|_| (c.bits(row_bits) as usize, c.bits(fib_bits) as usize))
		.collect()
}

pub fn proof_size(setup: &Setup, proof: &Proof, queries: &[(usize, usize)]) -> ProofSize {
	let p = &setup.params;
	let mut q_bytes = 0;
	for j in 0..p.folds() {
		let fib = p.fibres(j);
		let leaves: std::collections::BTreeSet<usize> = queries.iter().map(|&(x, q)| x * fib + (q >> j)).collect();
		q_bytes += leaves.len() * (64 + p.salt_bytes);
		q_bytes += 32 * multiproof_size(leaves.iter().copied(), p.log_n_parties() + p.m() - j - 1);
	}
	let tails = proof.tails.len() * (proof.tails[0].len() * 32 + p.salt_bytes);
	let frontend = 32 * (1 + proof.t.len() + 1 + 2 * proof.coeffs.len()) + 32 * (proof.roots.len() + 1);
	ProofSize { queries: q_bytes, tails, frontend, total: q_bytes + tails + frontend }
}

/// Self-contained proof verifier; it extracts the initial root from the proof.
/// Use `verify_committed` to open an independently supplied earlier commitment.
/// Checks (a)–(e) of Section 4.7 and the frontend check of Section 4.5.
pub fn verify<H: HashSuite>(setup: &Setup, inst: &Instance, proof: &Proof) -> Result<Vec<(usize, usize)>, String> {
    verify_bound::<H>(setup, inst, proof, &[])
}

pub fn verify_bound<H: HashSuite>(setup: &Setup, inst: &Instance, proof: &Proof, context: &[u8]) -> Result<Vec<(usize, usize)>, String> {
 let hasher=Hasher::<H>::default();
 let mut tr=Transcript::new(&hasher,&bound_instance(setup,inst,context));
 verify_in(setup,inst,proof,&mut tr,0)
}

/// Verifies an opening against the caller's earlier commitment and public context.
pub fn verify_committed<H:HashSuite>(setup:&Setup, commitment:&Hash, inst:&Instance, proof:&Proof, context:&[u8])->Result<Vec<(usize,usize)>,String> {
 if proof.roots.first()!=Some(commitment) {return Err("commitment mismatch".into());}
 verify_bound::<H>(setup,inst,proof,context)
}
pub fn verify_in<H:HashSuite>(setup:&Setup,inst:&Instance,proof:&Proof,tr:&mut Transcript<'_,H>,role:u64)->Result<Vec<(usize,usize)>,String> {
 let p=&setup.params;
 let folds=p.folds();
 let hasher=Hasher::<H>::scoped(role);
	let dummy2 = dummy_root(&hasher,2);
	let dummy3 = dummy_root(&hasher,3);
	let dummy4 = dummy_root(&hasher,4);
	if inst.r_h.len()!=crate::field::LOG_D || inst.r_a.len()!=setup.log_k() || inst.r_b.len()!=p.ell
        || proof.roots.len() != folds || proof.coeffs.len() != folds || proof.t.len() != D {
		return Err("malformed proof".into());
	}
	let alpha = tr.round(&proof.roots[0], l_bytes(&[proof.xi])).field();
	let mut c2 = tr.round(&dummy2, l_bytes(&proof.t));
	let r_pp: Vec<L> = (0..crate::field::LOG_D).map(|_| c2.field()).collect();
	let omega: Vec<L> = (0..setup.n_omega()).map(|_| c2.field()).collect();
	let eps = tr.round(&dummy3, l_bytes(&[proof.h_omega])).field();
	if eps == L::ZERO || omega.contains(&L::ZERO) {
		return Err("excluded challenge".into());
	}
	// Frontend: λ_r(T) = α s_x + ξ.
	let psi = chi_map(&inst.r_h);
	let lam_t: L = proof.t.iter().enumerate().map(|(u, &tu)| basis(u) * psi.apply(tu)).sum();
	if lam_t != alpha * inst.s_x + proof.xi {
		return Err("frontend check failed".into());
	}
	let chi_pp = eq_expand(&r_pp);
	let mut s: L = proof.t.iter().zip(&chi_pp).map(|(&tu, &c)| c * tu).sum::<L>() + eps * proof.h_omega;
	// Sumcheck rounds.
	let mut r = Vec::with_capacity(folds);
	for j in 0..folds {
		let (g0, g2) = proof.coeffs[j];
		let root = if j == 0 { dummy4 } else { proof.roots[j] };
		let rj = tr.round(&root, l_bytes(&[g0, g2])).field();
		if rj == L::ONE {
			return Err("excluded challenge".into());
		}
		s = g0 + (s + g2) * rj + g2 * rj * rj;
		r.push(rj);
	}
 let wf=verifier_weight(setup,inst,alpha,&r_pp,&omega,eps,&r);
 verify_backend(setup,proof,tr,&hasher,&r,&wf,s)
}
pub(crate) fn verify_backend<H:HashSuite>(setup:&Setup,proof:&Proof,tr:&mut Transcript<'_,H>,hasher:&Hasher<H>,r:&[L],wf:&[Vec<L>],s:L)->Result<Vec<(usize,usize)>,String> {
 let p=&setup.params;let (k,np,folds)=(p.k(),p.n_parties,p.folds());
	// (a) Tail root.
	if proof.tails.len() != np || proof.tail_salts.len() != np || proof.tails.iter().any(|t|t.len()!=1usize<<p.tau) {
		return Err("malformed tails".into());
	}
	let tail_leaves: Vec<Hash> = (0..np)
		.map(|i| hasher.at_layer(TAG_TAIL).leaf(TAG_TAIL, i as u64, l_bytes(&proof.tails[i]), &proof.tail_salts[i]))
		.collect();
	let tail_root = Tree::build(&hasher.at_layer(TAG_TAIL), tail_leaves).root();
	if tail_root != proof.tail_root {
		return Err("tail root mismatch".into());
	}
	let queries = sample_queries(setup, tr, &tail_root);
	if proof.openings.len() != queries.len() {
		return Err("wrong number of query openings".into());
	}
	// (a)–(c) per query.
	for (a, &(xa, qa)) in queries.iter().enumerate() {
		let ops = &proof.openings[a];
        if ops.len()!=folds { return Err("malformed query layers".into()); }
		for j in 0..folds {
			let op = &ops[j];
			let qj = qa >> j;
			let fib = p.fibres(j);
            if op.path.len()!=p.log_n_parties()+p.m()-j-1 { return Err("malformed Merkle path".into()); }
			let lh=hasher.at_layer(j as u64);let leaf = lh.leaf(j as u64, (xa * fib + qj) as u64, l_bytes(&op.values), &op.salt);
			if root_from_path(&lh, leaf, xa * fib + qj, &op.path) != proof.roots[j] {
				return Err(format!("Merkle path failed (query {a}, layer {j})"));
			}
			let folded = setup.row.fold_pair(p.m() - j, qj, op.values[0], op.values[1], r[j]);
			let next = if j + 1 < folds {
				ops[j + 1].values[qj & 1]
			} else {
				setup.row.encode(&proof.tails[xa])[qj]
			};
			if folded != next {
				return Err(format!("fold consistency failed (query {a}, layer {j})"));
			}
		}
	}
	// (d) Column decoding of the tails.
	let tl = 1 << p.tau;
	let mut logical = vec![vec![L::ZERO; tl]; k]; // X^{(ℓ-τ)}(y, u)
	for u in 0..tl {
		let shares: Vec<L> = proof.tails.iter().map(|t| t[u]).collect();
		let vals = setup.sharing.decode(&shares).ok_or("column decoding failed")?;
		for y in 0..k {
			logical[y][u] = vals[y];
		}
	}
	// (e) Endpoint with the folded logical weight.
	let end: L = (0..k).flat_map(|y| (0..tl).map(move |u| (y, u))).map(|(y, u)| wf[y][u] * logical[y][u]).sum();
	if end != s {
		return Err("endpoint check failed".into());
	}
	Ok(queries)
}

/// W^{(ℓ-τ)}(y, u) by the tensor contraction of Section 4.8 / Appendix E.
pub fn verifier_weight(
	setup: &Setup,
	inst: &Instance,
	alpha: L,
	r_pp: &[L],
	omega: &[L],
	eps: L,
	r: &[L],
) -> Vec<Vec<L>> {
	let p = &setup.params;
	let (k, jf, tl) = (p.k(), p.folds(), 1usize << p.tau);
	let phi = chi_map(r_pp);
	let chi_pp = eq_expand(r_pp);
	let ay: Vec<L> = eq_expand(&inst.r_a).iter().map(|&e| alpha * e).collect();
	let g: Vec<Vec<L>> = (0..k).map(|y| (0..D).map(|v| phi.apply(ay[y] * basis(v))).collect()).collect();
	let (rb_lo, rb_hi) = inst.r_b.split_at(jf);
	// E = Π_t ((1 - r_t) ⊗ (1 - ρ_t) + r_t ⊗ ρ_t).
	let mut e = Tensor::one();
	for t in 0..jf {
		e = e.mul_simple_sum(&[(L::ONE - r[t], L::ONE - rb_lo[t]), (r[t], rb_lo[t])]);
	}
	let fj = |x: usize| chi(x & ((1 << jf) - 1), r);
	let mut w = vec![vec![L::ZERO; tl]; k];
	let chi_hi = eq_expand(rb_hi);
	for u in 0..tl {
		let mut f = e.mul_right(chi_hi[u]);
		// Remove the padding columns folding into u.
		for &x in setup.layout.pad.iter().filter(|&&x| x >> jf == u) {
			let fx = fj(x);
			for v in bits_of(chi(x, &inst.r_b)) {
				f[v] -= fx;
			}
		}
		for y in 0..k {
			w[y][u] = (0..D).map(|v| g[y][v] * f[v]).sum();
		}
	}
	// Tensor masks: replace the data contribution.
	for masks in &setup.layout.masks {
		for m in masks {
			let gx = phi.apply(ay[m.y] * chi(m.x, &inst.r_b));
			w[m.y][m.x >> jf] += fj(m.x) * (chi_pp[m.h] - gx);
		}
	}
	// The public mask weight, folded through all ℓ - τ layers.
	for (x, mw) in setup.mask_weight(omega) {
		w[0][x >> jf] += eps * fj(x) * mw;
	}
	w
}

/// A fresh seed from the clock (benchmarks only; the prototype's randomness is not hardened).
pub fn rng_seed() -> u64 {
	let mut r = StdRng::seed_from_u64(
		std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos() as u64,
	);
	r.random()
}

#[cfg(test)]
mod tests {
	use binius_hash::Blake3HashSuite as Hs;

	use super::*;
	use crate::{params::Params, setup::random_instance};

	fn small() -> Setup {
		Setup::new(Params { n_parties: 4, ell: 11, beta: 2, gamma: 14, tau: 3, salt_bytes: 32 })
	}

	#[test]
	fn honest_proof_verifies() {
		for np in [4, 8, 16] {
			let setup = Setup::new(Params { n_parties: np, ell: 11, beta: 2, gamma: 14, tau: 3, salt_bytes: 32 });
			let (inst, wit) = random_instance(&setup, 50 + np as u64, None);
			let (proof, _, _) = prove::<Hs>(&setup, &inst, &wit, 7);
			verify::<Hs>(&setup, &inst, &proof).expect("honest proof must verify");
		}
	}

	#[test]
	fn share_based_frontend_matches_owners() {
		use crate::field::Random;
		for (np, seed, gamma, tau) in [(4,60u64,14,3),(8,61,14,3),(16,62,14,3),(16,63,14,3),(32,64,871,4)] {
            let setup = Setup::new(Params { n_parties: np, ell: 11, beta: 2, gamma, tau, salt_bytes: 32 });
			let (n, k) = (setup.params.n(), setup.params.k());
			let (inst, wit) = random_instance(&setup, seed, None);
			let mut parties: Vec<Party> = (0..np).map(|i| Party::new(i, n, seed + i as u64)).collect();
			let mut rng = StdRng::seed_from_u64(seed ^ 0xabc);
			for x in 0..n {
				let shares = if setup.layout.is_pad[x] {
					setup.sharing.random_shares(&mut rng)
				} else {
					let vals: Vec<L> = (0..k).map(|y| wit.get(n, y, x)).collect();
					setup.sharing.share(&vals, &mut rng)
				};
				for (i, sh) in shares.into_iter().enumerate() {
					parties[i].row[x] = sh;
				}
			}
			let xi_s: L = parties.iter_mut().map(|q| q.frontend(&setup, &inst, None)[0]).sum();
			let xi_o: L = parties.iter_mut().map(|q| q.frontend_owner(&setup, &wit, &inst, None)[0]).sum();
			assert_eq!(xi_s, xi_o, "ξ, N = {np}");
			let alpha = L::random(&mut rng);
			let sum = |parties: &mut Vec<Party>, owner: bool| {
				let mut t = vec![L::ZERO; D];
				for q in parties.iter_mut() {
					let ti = if owner {
						q.frontend_owner(&setup, &wit, &inst, Some(alpha))
					} else {
						q.frontend(&setup, &inst, Some(alpha))
					};
					for (a, b) in t.iter_mut().zip(ti) {
						*a += b;
					}
				}
				t
			};
			assert_eq!(sum(&mut parties, false), sum(&mut parties, true), "T, N = {np}");
		}
	}

    #[test]
    fn folded_global_mask_weights_match_explicit_table() {
        use crate::field::Random;
        for np in [4,16] {
            let setup=Setup::new(Params { n_parties:np,ell:11,beta:2,gamma:14,tau:3,salt_bytes:32 });
            let (inst,_)=random_instance(&setup,99,Some(0));
            let mut rng=StdRng::seed_from_u64(101);
            let alpha=L::random(&mut rng);let eps=L::random(&mut rng);
            let pp:Vec<L>=(0..8).map(|_|L::random(&mut rng)).collect();
            let omega:Vec<L>=(0..setup.n_omega()).map(|_|L::random(&mut rng)).collect();
            let r:Vec<L>=(0..setup.params.folds()).map(|_|L::random(&mut rng)).collect();
            let phi=chi_map(&pp);let ch=eq_expand(&pp);let ea=eq_expand(&inst.r_a);
            let mut direct:Vec<Vec<L>>=(0..setup.params.k()).map(|y|(0..setup.params.n()).map(|x| {
                if setup.layout.is_pad[x] {L::ZERO} else {phi.apply(alpha*ea[y]*chi(x,&inst.r_b))}
            }).collect()).collect();
            for m in setup.layout.masks.iter().flatten() { direct[m.y][m.x]=ch[m.h]; }
            for (x,w) in setup.mask_weight(&omega) { direct[0][x]+=eps*w; }
            for row in &mut direct {for &t in &r {*row=fold_coeffs(row,t);}}
            assert_eq!(verifier_weight(&setup,&inst,alpha,&pp,&omega,eps,&r),direct);
        }
    }

    #[test]
    fn released_mask_cells_are_committed_data_and_old_format_is_rejected() {
        let setup = Setup::new(Params { n_parties: 8, ell: 11, beta: 2, gamma: 14, tau: 3, salt_bytes: 32 });
        let (mut inst, _) = random_instance(&setup, 81, Some(0));
        let x = setup.layout.owned[1][0]; // formerly a tensor mask, now data
        let y = 0;
        let mut table = vec![L::ZERO; setup.params.k()*setup.params.n()];
        table[y*setup.params.n()+x] = L::ONE;
        let point = (inst.r_h.clone(),inst.r_a.clone(),inst.r_b.clone());
        inst.s_x = crate::setup::partial_claim(&setup,1,&table,&point);
        let expected = crate::field::chi(y,&inst.r_a)*crate::field::chi(x,&inst.r_b)
            * crate::algebra::chi_map(&inst.r_h).apply(L::ONE);
        assert_eq!(inst.s_x, expected);
        assert_ne!(inst.s_x,L::ZERO);
        let wit = crate::setup::Witness { table };
        let (proof,_,_) = prove::<Hs>(&setup,&inst,&wit,83);
        verify::<Hs>(&setup,&inst,&proof).unwrap();
        let mut encoded = crate::pcs_codec::encode_proof(&proof);
        let decoded = crate::pcs_codec::decode_proof(&setup,&encoded).unwrap();
        verify::<Hs>(&setup,&inst,&decoded).unwrap();
        encoded[..8].copy_from_slice(b"B2PCS001");
        assert!(crate::pcs_codec::decode_proof(&setup,&encoded).is_err());
        inst.s_x=L::ZERO;
        assert!(verify::<Hs>(&setup,&inst,&proof).is_err());
    }

	#[test]
	fn tampering_is_rejected() {
		let setup = small();
		let (inst, wit) = random_instance(&setup, 51, None);
		let (proof, _, _) = prove::<Hs>(&setup, &inst, &wit, 8);

		let mut bad = inst.clone();
		bad.s_x += L::ONE;
		assert!(verify::<Hs>(&setup, &bad, &proof).is_err(), "wrong claim");

		let tamper = |f: &dyn Fn(&mut Proof)| {
			let (mut pr, _, _) = prove::<Hs>(&setup, &inst, &wit, 8);
			f(&mut pr);
			verify::<Hs>(&setup, &inst, &pr).is_err()
		};
		assert!(tamper(&|pr| pr.t[3] += L::ONE), "tensor");
		assert!(tamper(&|pr| pr.h_omega += L::ONE), "mask sum");
		assert!(tamper(&|pr| pr.coeffs[2].0 += L::ONE), "round polynomial");
		assert!(tamper(&|pr| pr.tails[1][0] += L::ONE), "tail");
		assert!(tamper(&|pr| pr.openings[0][1].values[0] += L::ONE), "opened value");
	}
}

#[cfg(test)]
mod bound_tests {
    use super::*;
    use binius_hash::Blake3HashSuite;
    #[test]
    fn precommit_and_context_binding() {
        let setup=Setup::new(crate::params::Params{n_parties:8,ell:12,beta:2,gamma:16,tau:3,salt_bytes:32});
        let (inst,wit)=crate::setup::random_instance(&setup,19,Some(16));
        let prepared=prepare::<Blake3HashSuite>(&setup,&wit,23);
        let root=prepared.root;
        let (proof,_,_)=open_prepared::<Blake3HashSuite>(&setup,&inst,prepared,b"PIOP transcript");
        assert_eq!(proof.roots[0],root);
        assert!(verify_bound::<Blake3HashSuite>(&setup,&inst,&proof,b"PIOP transcript").is_ok());
        assert!(verify_bound::<Blake3HashSuite>(&setup,&inst,&proof,b"different transcript").is_err());
        let mut bad=proof.clone();bad.tails[0].pop();
        assert!(verify_bound::<Blake3HashSuite>(&setup,&inst,&bad,b"PIOP transcript").is_err());
    }
}

#[cfg(test)]
mod frontend_setbits_tests {
    use super::*;
    use crate::{field::Random,params::Params,setup::random_instance};
    #[test]
    fn set_bit_frontend_matches_original_for_full_vectors() {
        let mut rng=StdRng::seed_from_u64(20261029);
        for np in [8,16,32] {
            let setup=Setup::new(Params{n_parties:np,ell:12,beta:2,gamma:16,tau:3,salt_bytes:32});
            let (base,_)=random_instance(&setup,177,None);
            for id in [0,np-1] {for cached in [false,true] {for zero_row in [false,true] {for boolean_point in [false,true] {
                let mut inst=base.clone();if boolean_point {inst.r_a.fill(L::ZERO);inst.r_b.fill(L::ZERO);}
                for alpha in [L::ZERO,L::ONE,L::random(&mut rng)] {
                    let row=(0..setup.params.n()).map(|_|if zero_row {L::ZERO}else{L::random(&mut rng)}).collect::<Vec<_>>();
                    let mut a=Party::new(id,setup.params.n(),0);a.row=row.clone();
                    let mut b=Party::new(id,setup.params.n(),0);b.row=row;
                    if cached {a.eb=eq_expand(&inst.r_b);b.eb=a.eb.clone();}
                    let expected=a.frontend_reference(&setup,&inst,Some(alpha));
                    let got=b.frontend(&setup,&inst,Some(alpha));
                    assert_eq!(got,expected);assert_eq!(a.eb,b.eb);
                }
            }}}}
        }
    }
}

#[cfg(test)]
mod standalone_v4_tests {
 use super::*;
 use binius_hash::{Blake3HashSuite,Sha256HashSuite};
 fn check<H:HashSuite>() {
  let setup=Setup::new(crate::params::Params{n_parties:8,ell:11,beta:2,gamma:14,tau:3,salt_bytes:32});
  let (inst,wit)=crate::setup::random_instance(&setup,2301,Some(1024));
  let prepared=prepare::<H>(&setup,&wit,2303);let commitment=prepared.root;
  let (proof,_,_)=open_prepared::<H>(&setup,&inst,prepared,b"fixed upper statement");
  let encoded=crate::pcs_codec::encode_proof(&proof);
  assert_eq!(&encoded[..8],b"B2PCS004");
  let decoded=crate::pcs_codec::decode_proof(&setup,&encoded).unwrap();
  assert!(verify_bound::<H>(&setup,&inst,&decoded,b"fixed upper statement").is_ok());
  assert!(verify_committed::<H>(&setup,&commitment,&inst,&decoded,b"fixed upper statement").is_ok());
  let mut other=commitment;other[0]^=1;
  assert_eq!(verify_committed::<H>(&setup,&other,&inst,&decoded,b"fixed upper statement"),Err("commitment mismatch".into()));
  assert!(verify_bound::<H>(&setup,&inst,&decoded,b"other statement").is_err());
  let mut old=encoded.clone();old[..8].copy_from_slice(b"B2PCS003");assert!(crate::pcs_codec::decode_proof(&setup,&old).is_err());
  let mutations:Vec<Box<dyn Fn(&mut Proof)>>=vec![
   Box::new(|p|p.roots[0][0]^=1),Box::new(|p|p.roots[1][0]^=1),
   Box::new(|p|p.xi+=L::ONE),Box::new(|p|p.t[0]+=L::ONE),Box::new(|p|p.h_omega+=L::ONE),
   Box::new(|p|p.coeffs[0].0+=L::ONE),Box::new(|p|p.coeffs[1].1+=L::ONE),
   Box::new(|p|p.tail_root[0]^=1),Box::new(|p|p.tails[0][0]+=L::ONE),Box::new(|p|p.tail_salts[0][0]^=1),
   Box::new(|p|p.openings[0][0].values[0]+=L::ONE),Box::new(|p|p.openings[0][0].salt[0]^=1),Box::new(|p|p.openings[0][0].path[0][0]^=1),
   Box::new(|p|{p.roots.pop();}),Box::new(|p|{p.t.pop();}),Box::new(|p|{p.coeffs.pop();}),
   Box::new(|p|{p.tails.pop();}),Box::new(|p|{p.tail_salts.pop();}),Box::new(|p|{p.tails[0].pop();}),
   Box::new(|p|{p.openings.pop();}),Box::new(|p|{p.openings[0].pop();}),Box::new(|p|{p.openings[0][0].path.pop();}),
  ];
  for (i,mutate) in mutations.into_iter().enumerate(){let mut bad=proof.clone();mutate(&mut bad);assert!(verify_bound::<H>(&setup,&inst,&bad,b"fixed upper statement").is_err(),"accepted mutation {i}");}
  let mut bad=inst.clone();bad.s_x+=L::ONE;assert!(verify_bound::<H>(&setup,&bad,&proof,b"fixed upper statement").is_err());
  bad=inst.clone();bad.r_b.pop();assert!(verify_bound::<H>(&setup,&bad,&proof,b"fixed upper statement").is_err());
 }
 #[test] fn complete_standalone_roundtrip_and_24_negative_cases_per_suite(){check::<Blake3HashSuite>();check::<Sha256HashSuite>();}
 #[test] fn parameters_context_and_dummy_rounds_are_bound(){
  let p=crate::params::Params{n_parties:8,ell:11,beta:2,gamma:14,tau:3,salt_bytes:32};let mut s=Setup::new(p.clone());
  let(inst,_)=crate::setup::random_instance(&s,19,Some(0));let base=bound_instance(&s,&inst,b"ctx");
  for i in 0..6 {s.params=p.clone();match i {0=>s.params.n_parties+=1,1=>s.params.ell+=1,2=>s.params.beta+=1,3=>s.params.gamma+=1,4=>s.params.tau+=1,_=>s.params.salt_bytes+=1};assert_ne!(base,bound_instance(&s,&inst,b"ctx"));}
  let h=Hasher::<Blake3HashSuite>::default();assert_ne!(dummy_root(&h,2),dummy_root(&h,3));assert_ne!(dummy_root(&h,3),dummy_root(&h,4));
  for role in [1,2] {let h=Hasher::<Blake3HashSuite>::scoped(role);assert_eq!(dummy_root(&h,2),h.leaf(u64::MAX,0,&[0],&[]));assert_eq!(dummy_root(&h,2),dummy_root(&h,4));}
 }
}
