//! Collaborative Spartan-type PIOP over L for a uniform R1CS over F2, simulated in one process
//! (design: `b2-design/collab-snark/DESIGN.md`, interfaces: `DERIVATIONS.md` v0.3).
//!
//! Version 1 covers the two sumchecks without zero-knowledge masks and without the PCS
//! opening; it checks correctness against the plaintext and times each party's local work.
//!
//! * Relation: C copies of a base circuit (A0, B0, C0) over F2, (A z) ∘ (B z) = C z.
//!   Copy c = g + G·y: the slot y < k is the packed-Shamir slot, g < G a copy group.
//! * Sharing: every bit vector (z, Az, Bz, Cz) is shared per bit, packed over the slot y, with
//!   values in the subfield B (degree < k', random tail in B).
//! * Sumcheck #1 over (j, g) (column rounds): each party runs a plain sumcheck on its shares;
//!   share products have degree ≤ N - 2, so the slot sum with weights eq(τ_y, ·) is a fixed
//!   linear combination of the N local values (weighted reconstruction, through F_Agg).
//! * Sumcheck #1 over y (slot rounds): the folded packed values of Az, Bz, Cz are converted to
//!   k ordinary Shamir sharings with dealer-provided double sharings (PSS→SSS).
//! * Sumcheck #2 runs only over the in-copy position p: the weight is w0(p) ⊗ eq(r_c, c), so
//!   it ends at z̃(r_p, r_g, r_y), the single claim for the PCS.

use std::time::{Duration, Instant};

use binius_field::arithmetic_traits::InvertOrZero;
use rand::{Rng, RngExt, SeedableRng, rngs::StdRng};

use crate::{
	code::ColCode,
	field::{B, Field, L, Random, eq_expand, from_b, mul_b},
	sharing::Sharing,
};

/// A base circuit over F2: row j of A0 is the XOR of the positions in `a[j]`.
#[derive(Clone, Debug)]
pub struct Base {
	pub log_m0: usize,
	pub log_n0: usize,
	pub a: Vec<Vec<usize>>,
	pub b: Vec<Vec<usize>>,
	pub c: Vec<Vec<usize>>,
}

impl Base {
	pub fn m0(&self) -> usize {
		1 << self.log_m0
	}
	pub fn n0(&self) -> usize {
		1 << self.log_n0
	}

	/// A random AND/XOR circuit shaped like hashing circuits in R1CS over F2: n_in = m0 input
	/// positions, then one AND output per constraint; each AND input is the XOR of `fanin`
	/// earlier positions.
	pub fn random(log_m0: usize, fanin: usize, rng: &mut impl Rng) -> Self {
		let m0 = 1 << log_m0;
		let n_in = m0;
		let (mut a, mut b, mut c) = (Vec::with_capacity(m0), Vec::with_capacity(m0), Vec::with_capacity(m0));
		for j in 0..m0 {
			let avail = n_in + j;
			let pick = |rng: &mut dyn rand::Rng| -> Vec<usize> {
				let mut v: Vec<usize> = (0..fanin).map(|_| rng.random_range(0..avail)).collect();
				v.sort_unstable();
				v.dedup();
				v
			};
			a.push(pick(&mut *rng));
			b.push(pick(&mut *rng));
			c.push(vec![n_in + j]);
		}
		Self { log_m0, log_n0: log_m0 + 1, a, b, c }
	}

	/// A satisfying assignment for one copy from random inputs, with the row values (Az, Bz, Cz).
	pub fn witness(&self, rng: &mut impl Rng) -> (Vec<bool>, [Vec<bool>; 3]) {
		let m0 = self.m0();
		let mut z = vec![false; self.n0()];
		for x in z.iter_mut().take(m0) {
			*x = rng.random();
		}
		let lin = |z: &[bool], row: &[usize]| row.iter().fold(false, |acc, &p| acc ^ z[p]);
		let (mut va, mut vb, mut vc) = (vec![false; m0], vec![false; m0], vec![false; m0]);
		for j in 0..m0 {
			va[j] = lin(&z, &self.a[j]);
			vb[j] = lin(&z, &self.b[j]);
			z[m0 + j] = va[j] & vb[j];
			vc[j] = z[m0 + j];
		}
		(z, [va, vb, vc])
	}

	/// w0(p) = Σ_j eq(r_j, j)(ρ_A A0 + ρ_B B0 + ρ_C C0)[j, p] for all p.
	pub fn weight(&self, eq_j: &[L], rho: [L; 3]) -> Vec<L> {
		let mut w = vec![L::ZERO; self.n0()];
		for (mat, &r) in [&self.a, &self.b, &self.c].into_iter().zip(&rho) {
			for (j, row) in mat.iter().enumerate() {
				let s = eq_j[j] * r;
				for &p in row {
					w[p] += s;
				}
			}
		}
		w
	}
}

/// Actual Gao–Mateer evaluation nodes of the column code. A unit novel-basis
/// coefficient is not a coordinate map and may repeat values across nodes.
fn pseudo_nodes(col: &ColCode) -> Vec<L> {
    binius_math::ReedSolomonCode::<B>::new(col.log_kp, 2)
        .subspace().iter().map(from_b).collect()
}

#[cfg(test)]
std::thread_local! { static LAGRANGE_AT_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
/// Lagrange weights over public interpolation nodes.
fn lagrange_at(xs: &[L], t: L) -> Vec<L> {
    #[cfg(test)] LAGRANGE_AT_CALLS.with(|n|n.set(n.get()+1));
	(0..xs.len())
		.map(|i| {
			let (mut num, mut den) = (L::ONE, L::ONE);
			for (j, &xj) in xs.iter().enumerate() {
				if j != i {
					num *= t - xj;
					den *= xs[i] - xj;
				}
			}
			num * den.invert_or_zero()
		})
		.collect()
}

/// Sharing tools at the PCS's nodes.
pub struct Ctx {
	pub n: usize,
	pub k: usize,
	pub kp: usize,
	sharing: Sharing,
	/// share_i = Σ_{y<k'} share_mat[i][y] · value_y (value_y at η_y; B-valued).
	share_mat: Vec<Vec<B>>,
    /// Fixed degree<k' packed reconstruction; distinct from lag_n.
    lag_packed: Vec<Vec<L>>,
	/// lag_n[i][y]: P(η_y) = Σ_i lag_n[i][y] P(ζ_i) for deg P < N.
	pub lag_n: Vec<Vec<L>>,
	zeta: Vec<L>,
	eta0: L,
	/// Degree t' = N/4 of the ordinary sharings.
	pub t_sss: usize,
}

fn b_of(x: L) -> B {
	crate::field::coords(x)[0]
}

impl Ctx {
	pub fn new(n: usize) -> Self {
		let sharing = Sharing::new(n);
		let (k, kp) = (n / 4, n / 2);
		let col = ColCode::new(kp.trailing_zeros() as usize);
		let nodes = pseudo_nodes(&col);
		let eta: Vec<L> = nodes[..kp].to_vec();
		let zeta: Vec<L> = nodes[kp..3 * kp].to_vec();
		// share_mat: images of unit vectors on coset 0.
		let mut share_mat = vec![vec![B::ZERO; kp]; n];
		for y in 0..kp {
			let mut e = vec![L::ZERO; kp];
			e[y] = L::ONE;
			let sh = col.evaluate(&col.interpolate(&e, 0));
			for i in 0..n {
				share_mat[i][y] = b_of(sh[kp + i]);
			}
		}
		let lag_n_t: Vec<Vec<L>> = (0..k).map(|y| lagrange_at(&zeta, eta[y])).collect();
		let lag_n = (0..n).map(|i| (0..k).map(|y| lag_n_t[y][i]).collect()).collect();
		let lag_packed = (0..kp).map(|i| sharing.lagrange(i)).collect();
        prepare_interpolation();
        Self { n, k, kp, sharing, share_mat, lag_packed, lag_n, zeta, eta0: eta[0], t_sss: n / 4 }
	}

	/// Shares (B-valued) of k bits packed over the slots, random tail in B.
	pub fn share_bits(&self, bits: impl Fn(usize) -> bool, rng: &mut impl Rng, out: &mut [B]) {
		let tail: Vec<B> = (self.k..self.kp).map(|_| B::random(&mut *rng)).collect();
		for (i, o) in out.iter_mut().enumerate() {
			let row = &self.share_mat[i];
			let mut s = B::ZERO;
			for y in 0..self.k {
				if bits(y) {
					s += row[y];
				}
			}
			for (y, &u) in tail.iter().enumerate() {
				s += row[self.k + y] * u;
			}
			*o = s;
		}
	}

	/// Packed shares of k values of L, random tail in L (degree < k').
	pub fn share_packed(&self, vals: &[L], rng: &mut impl Rng) -> Vec<L> {
		self.sharing.share(vals, rng)
	}

	/// Reconstructs k values from N packed shares of degree < k'.
	pub fn open_packed(&self, shares: &[L]) -> Vec<L> {
		(0..self.k).map(|y| (0..self.kp).map(|i| self.lag_packed[i][y] * shares[i]).sum()).collect()
	}

	/// Ordinary Shamir shares of v at η_0, degree t'.
	pub fn share_sss(&self, v: L, rng: &mut impl Rng) -> Vec<L> {
		let h: Vec<L> = (0..self.t_sss).map(|_| L::random(&mut *rng)).collect();
		self.zeta
			.iter()
			.map(|&x| {
				let d = x - self.eta0;
				let mut acc = L::ZERO;
				for &c in h.iter().rev() {
					acc = acc * x + c;
				}
				v + d * acc
			})
			.collect()
	}

	/// Weights for the secret at η_0 of a degree < N sharing.
	pub fn lag_eta0(&self) -> Vec<L> {
		lagrange_at(&self.zeta, self.eta0)
	}
}

/// Evaluation points of the round polynomials: 0, 1, ω, ω + 1 with ω ∈ B.
pub fn omega() -> B {
	B::MULTIPLICATIVE_GENERATOR
}

/// Value at r of the polynomial of degree ≤ 3 (or ≤ 2 if `vals.len() == 3`) with the given
/// values at 0, 1, ω, ω+1.
fn interpolation_denominators() -> &'static [[L;4];5] {
    static DEN: std::sync::OnceLock<[[L;4];5]> = std::sync::OnceLock::new();
    DEN.get_or_init(|| {
        let w=from_b(omega());let points=[L::ZERO,L::ONE,w,w+L::ONE];
        std::array::from_fn(|len| std::array::from_fn(|i| {
            if i>=len {L::ZERO} else {
                points[..len].iter().enumerate().filter(|(j,_)|*j!=i)
                    .map(|(_,x)|points[i]-*x).product::<L>().invert_or_zero()
            }
        }))
    })
}
/// Called with public context preparation, before any online transcript work.
pub(crate) fn prepare_interpolation() { let _=interpolation_denominators(); }
pub fn interp(vals: &[L], r: L) -> L {
    let w=from_b(omega());let points=[L::ZERO,L::ONE,w,w+L::ONE];
    let points=&points[..vals.len()];let den=&interpolation_denominators()[vals.len()];
    vals.iter().enumerate().map(|(i,v)| {
        let num:L=points.iter().enumerate().filter(|(j,_)|*j!=i).map(|(_,x)|r-*x).product();
        num * den[i] * *v
    }).sum()
}

/// eq(a, b) = Π (a_t b_t + (1 - a_t)(1 - b_t)).
pub fn eq_eval(a: &[L], b: &[L]) -> L {
	a.iter().zip(b).map(|(&x, &y)| x * y + (L::ONE - x) * (L::ONE - y)).product()
}

/// One party's shares.
pub struct PartyShares {
	pub z: Vec<B>,
	pub rows: [Vec<B>; 3],
}

/// Timings of one party.
#[derive(Clone, Debug, Default)]
pub struct PTimes {
	pub sc1_col: Duration,
	pub sc1_slot: Duration,
	pub sc2_prep: Duration,
	pub sc2: Duration,
}

impl PTimes {
	pub fn total(&self) -> Duration {
		self.sc1_col + self.sc1_slot + self.sc2_prep + self.sc2
	}
}

/// Round values of Σ eq · (a·b + c) (char 2) at 0, 1, ω, ω+1 on B-valued tables.
pub(crate) fn round_b(eq: &[L], a: &[B], b: &[B], c: &[B]) -> [L; 4] {
	let w = omega();
	let mut s = [L::ZERO; 4];
	for i in 0..eq.len() / 2 {
		let (e0, e1) = (eq[2 * i], eq[2 * i + 1]);
		let (a0, a1, b0, b1, c0, c1) = (a[2 * i], a[2 * i + 1], b[2 * i], b[2 * i + 1], c[2 * i], c[2 * i + 1]);
		let (da, db, dc) = (a0 + a1, b0 + b1, c0 + c1);
		let de = e0 + e1;
		let (aw, bw, cw) = (a0 + w * da, b0 + w * db, c0 + w * dc);
		let ew = e0 + mul_b(de, w);
		let (aw1, bw1, cw1) = (aw + da, bw + db, cw + dc);
		s[0] += mul_b(e0, a0 * b0 + c0);
		s[1] += mul_b(e1, a1 * b1 + c1);
		s[2] += mul_b(ew, aw * bw + cw);
		s[3] += mul_b(ew + de, aw1 * bw1 + cw1);
	}
	s
}

/// Same on L-valued tables.
pub(crate) fn round_l(eq: &[L], a: &[L], b: &[L], c: &[L]) -> [L; 4] {
	let w = omega();
	let mut s = [L::ZERO; 4];
	for i in 0..eq.len() / 2 {
		let (e0, e1) = (eq[2 * i], eq[2 * i + 1]);
		let (a0, a1, b0, b1, c0, c1) = (a[2 * i], a[2 * i + 1], b[2 * i], b[2 * i + 1], c[2 * i], c[2 * i + 1]);
		let (da, db, dc, de) = (a0 + a1, b0 + b1, c0 + c1, e0 + e1);
		let (aw, bw, cw, ew) = (a0 + mul_b(da, w), b0 + mul_b(db, w), c0 + mul_b(dc, w), e0 + mul_b(de, w));
		s[0] += e0 * (a0 * b0 + c0);
		s[1] += e1 * (a1 * b1 + c1);
		s[2] += ew * (aw * bw + cw);
		s[3] += (ew + de) * ((aw + da) * (bw + db) + cw + dc);
	}
	s
}

pub(crate) fn fold_b(v: &[B], r: L) -> Vec<L> {
	v.chunks_exact(2).map(|p| from_b(p[0]) + mul_b(r, p[0] + p[1])).collect()
}

pub(crate) fn fold_l(v: &[L], r: L) -> Vec<L> {
	v.chunks_exact(2).map(|p| p[0] + (p[1] - p[0]) * r).collect()
}

/// Result of a run.
pub struct Run {
	pub times: Vec<PTimes>,
	pub client: Duration,
	pub ok: bool,
	pub m: usize,
	pub z_len: usize,
	pub verifier: Duration,
}

/// Runs the two sumchecks on `copies = k·G` copies of `base` with N parties.
pub fn run(base: &Base, n: usize, log_g: usize, seed: u64) -> Run {
	let mut rng = StdRng::seed_from_u64(seed);
	let ctx = Ctx::new(n);
	let (k, g) = (ctx.k, 1usize << log_g);
	let (m0, n0) = (base.m0(), base.n0());
	let log_k = k.trailing_zeros() as usize;

	// Plaintext witness, copy c = g + G·y.
	let copies: Vec<(Vec<bool>, [Vec<bool>; 3])> = (0..k * g).map(|_| base.witness(&mut rng)).collect();

	// Client: per-bit packed sharing.
	let t0 = Instant::now();
	let mut parties: Vec<PartyShares> = (0..n)
		.map(|_| PartyShares { z: vec![B::ZERO; n0 * g], rows: [vec![B::ZERO; m0 * g], vec![B::ZERO; m0 * g], vec![B::ZERO; m0 * g]] })
		.collect();
	let mut buf = vec![B::ZERO; n];
	for gg in 0..g {
		for p in 0..n0 {
			ctx.share_bits(|y| copies[gg + g * y].0[p], &mut rng, &mut buf);
			for i in 0..n {
				parties[i].z[p + n0 * gg] = buf[i];
			}
		}
		for t in 0..3 {
			for j in 0..m0 {
				ctx.share_bits(|y| copies[gg + g * y].1[t][j], &mut rng, &mut buf);
				for i in 0..n {
					parties[i].rows[t][j + m0 * gg] = buf[i];
				}
			}
		}
	}
	let client = t0.elapsed();

	let mut times = vec![PTimes::default(); n];
	let mut ok = true;
	let lag_e0 = ctx.lag_eta0();

	// ---------------- Sumcheck #1 ----------------
	let nv_col = base.log_m0 + log_g;
	let tau: Vec<L> = (0..nv_col + log_k).map(|_| L::random(&mut rng)).collect();
	let (tau_col, tau_y) = tau.split_at(nv_col);
	let eq_col = eq_expand(tau_col);
	let eq_y = eq_expand(tau_y);
	let mu: Vec<L> = (0..n).map(|i| (0..k).map(|y| eq_y[y] * ctx.lag_n[i][y]).sum()).collect();

	let mut claim = L::ZERO; // Σ eq·(Az·Bz − Cz) = 0
	let mut r_col = Vec::with_capacity(nv_col);
	// Per-party folded tables.
	let mut st: Vec<(Vec<L>, [Vec<L>; 3])> = Vec::with_capacity(n);
	for _ in 0..n {
		st.push((Vec::new(), [Vec::new(), Vec::new(), Vec::new()]));
	}
	for round in 0..nv_col {
		let mut agg = [L::ZERO; 4];
		let mut locals = Vec::with_capacity(n);
		for i in 0..n {
			let t = Instant::now();
			let s = if round == 0 {
				let [a, b, c] = &parties[i].rows;
				round_b(&eq_col, a, b, c)
			} else {
				let (e, [a, b, c]) = &st[i];
				round_l(e, a, b, c)
			};
			times[i].sc1_col += t.elapsed();
			locals.push(s);
		}
		for i in 0..n {
			for u in 0..4 {
				agg[u] += mu[i] * locals[i][u];
			}
		}
		ok &= agg[0] + agg[1] == claim;
		let r = L::random(&mut rng);
		claim = interp(&agg, r);
		r_col.push(r);
		for i in 0..n {
			let t = Instant::now();
			if round == 0 {
				let [a, b, c] = &parties[i].rows;
				st[i] = (fold_l(&eq_col, r), [fold_b(a, r), fold_b(b, r), fold_b(c, r)]);
			} else {
				let (e, [a, b, c]) = &st[i];
				st[i] = (fold_l(e, r), [fold_l(a, r), fold_l(b, r), fold_l(c, r)]);
			}
			times[i].sc1_col += t.elapsed();
		}
	}
	let eq_col_r = st[0].0[0]; // eq(τ_col, r_col), public

	// PSS→SSS: dealer double sharings; open a − ρ.
	let mut sss: Vec<[Vec<L>; 3]> = (0..n).map(|_| [vec![L::ZERO; k], vec![L::ZERO; k], vec![L::ZERO; k]]).collect();
	for t in 0..3 {
		let rho: Vec<L> = (0..k).map(|_| L::random(&mut rng)).collect();
		let packed = ctx.share_packed(&rho, &mut rng);
		let per_slot: Vec<Vec<L>> = rho.iter().map(|&v| ctx.share_sss(v, &mut rng)).collect();
		let masked: Vec<L> = (0..n).map(|i| st[i].1[t][0] - packed[i]).collect();
		let delta = ctx.open_packed(&masked);
		for i in 0..n {
			let tm = Instant::now();
			for y in 0..k {
				sss[i][t][y] = delta[y] + per_slot[y][i];
			}
			times[i].sc1_slot += tm.elapsed();
		}
	}

	// Slot rounds on ordinary shares.
	let mut eq_slot: Vec<Vec<L>> = (0..n).map(|_| eq_y.iter().map(|&e| e * eq_col_r).collect()).collect();
	let mut r_y = Vec::with_capacity(log_k);
	for _ in 0..log_k {
		let mut agg = [L::ZERO; 4];
		for i in 0..n {
			let t = Instant::now();
			let [a, b, c] = &sss[i];
			let s = round_l(&eq_slot[i], a, b, c);
			times[i].sc1_slot += t.elapsed();
			for u in 0..4 {
				agg[u] += lag_e0[i] * s[u];
			}
		}
		ok &= agg[0] + agg[1] == claim;
		let r = L::random(&mut rng);
		claim = interp(&agg, r);
		r_y.push(r);
		for i in 0..n {
			let t = Instant::now();
			eq_slot[i] = fold_l(&eq_slot[i], r);
			for v in sss[i].iter_mut() {
				*v = fold_l(v, r);
			}
			times[i].sc1_slot += t.elapsed();
		}
	}
	let v: [L; 3] = std::array::from_fn(|t| (0..n).map(|i| lag_e0[i] * sss[i][t][0]).sum());
	let rx: Vec<L> = r_col.iter().chain(&r_y).copied().collect();
	ok &= claim == eq_eval(&tau, &rx) * (v[0] * v[1] + v[2]);

	// Plaintext check of the endpoints.
	{
		let ex = eq_expand(&rx);
		for t in 0..3 {
			let mut s = L::ZERO;
			for c in 0..k * g {
				let (gg, y) = (c % g, c / g);
				for j in 0..m0 {
					if copies[c].1[t][j] {
						s += ex[j + m0 * gg + m0 * g * y];
					}
				}
			}
			ok &= s == v[t];
		}
	}

	// ---------------- Sumcheck #2 ----------------
	let rho: [L; 3] = std::array::from_fn(|_| L::random(&mut rng));
	let mut claim2 = rho[0] * v[0] + rho[1] * v[1] + rho[2] * v[2];
	let (r_j, r_g) = r_col.split_at(base.log_m0);
	let eq_j = eq_expand(r_j);
	let eq_g = eq_expand(r_g);
	let eq_ry = eq_expand(&r_y);
	let mu2: Vec<L> = (0..n).map(|i| (0..k).map(|y| eq_ry[y] * ctx.lag_n[i][y]).sum()).collect();
	let mut zs: Vec<Vec<L>> = Vec::with_capacity(n);
	let mut ws: Vec<Vec<L>> = Vec::with_capacity(n);
	for i in 0..n {
		let t = Instant::now();
		let w0 = base.weight(&eq_j, rho);
		let mut zi = vec![L::ZERO; n0];
		for gg in 0..g {
			let e = eq_g[gg];
			let src = &parties[i].z[n0 * gg..n0 * (gg + 1)];
			for (d, &s) in zi.iter_mut().zip(src) {
				*d += mul_b(e, s);
			}
		}
		times[i].sc2_prep += t.elapsed();
		zs.push(zi);
		ws.push(w0);
	}
	let w = from_b(omega());
	let mut r_p = Vec::with_capacity(base.log_n0);
	for _ in 0..base.log_n0 {
		let mut agg = [L::ZERO; 3];
		for i in 0..n {
			let t = Instant::now();
			let (wv, zv) = (&ws[i], &zs[i]);
			let mut s = [L::ZERO; 3];
			for q in 0..wv.len() / 2 {
				let (w0_, w1_, z0, z1) = (wv[2 * q], wv[2 * q + 1], zv[2 * q], zv[2 * q + 1]);
				s[0] += w0_ * z0;
				s[1] += w1_ * z1;
				s[2] += (w0_ + w * (w0_ + w1_)) * (z0 + w * (z0 + z1));
			}
			times[i].sc2 += t.elapsed();
			for u in 0..3 {
				agg[u] += mu2[i] * s[u];
			}
		}
		ok &= agg[0] + agg[1] == claim2;
		let r = L::random(&mut rng);
		claim2 = interp(&agg, r);
		r_p.push(r);
		for i in 0..n {
			let t = Instant::now();
			ws[i] = fold_l(&ws[i], r);
			zs[i] = fold_l(&zs[i], r);
			times[i].sc2 += t.elapsed();
		}
	}
	let s_x: L = (0..n).map(|i| mu2[i] * zs[i][0]).sum();

	// Verifier: w̃0(r_p) from the base circuit, then the final check; s_x is the PCS claim.
	let tv = Instant::now();
	let w_rp = {
		let wv = base.weight(&eq_j, rho);
		let ep = eq_expand(&r_p);
		wv.iter().zip(&ep).map(|(a, b)| *a * *b).sum::<L>()
	};
	ok &= claim2 == w_rp * s_x;
	let verifier = tv.elapsed();

	// Plaintext check of s_x = z̃(r_p, r_g, r_y).
	{
		let pt: Vec<L> = r_p.iter().chain(r_g).chain(&r_y).copied().collect();
		let ex = eq_expand(&pt);
		let mut s = L::ZERO;
		for c in 0..k * g {
			let (gg, y) = (c % g, c / g);
			for p in 0..n0 {
				if copies[c].0[p] {
					s += ex[p + n0 * gg + n0 * g * y];
				}
			}
		}
		ok &= s == s_x;
	}

	Run { times, client, ok, m: m0 * k * g, z_len: n0 * k * g, verifier }
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn lagrange_over_all_nodes_matches_sharing() {
		let mut rng = StdRng::seed_from_u64(40);
		let ctx = Ctx::new(16);
		let vals: Vec<L> = (0..4).map(|_| L::random(&mut rng)).collect();
		let sh = ctx.share_packed(&vals, &mut rng);
		for y in 0..4 {
			let rec: L = (0..16).map(|i| ctx.lag_n[i][y] * sh[i]).sum();
			assert_eq!(rec, vals[y]);
		}
		let v = L::random(&mut rng);
		let s = ctx.share_sss(v, &mut rng);
		let e0 = ctx.lag_eta0();
		assert_eq!((0..16).map(|i| e0[i] * s[i]).sum::<L>(), v);
	}

	#[test]
	fn product_of_packed_shares_reconstructs() {
		let mut rng = StdRng::seed_from_u64(41);
		let ctx = Ctx::new(16);
		let mut a = vec![B::ZERO; 16];
		let mut b = vec![B::ZERO; 16];
		let ab = [true, false, true, true];
		let bb = [true, true, false, true];
		ctx.share_bits(|y| ab[y], &mut rng, &mut a);
		ctx.share_bits(|y| bb[y], &mut rng, &mut b);
		for y in 0..4 {
			let rec: L = (0..16).map(|i| ctx.lag_n[i][y] * from_b(a[i] * b[i])).sum();
			assert_eq!(rec, if ab[y] & bb[y] { L::ONE } else { L::ZERO });
		}
	}

	#[test]
	fn two_sumchecks_end_to_end() {
		let mut rng = StdRng::seed_from_u64(42);
		let base = Base::random(6, 4, &mut rng);
		for (n, log_g) in [(8, 1), (16, 2)] {
			let r = run(&base, n, log_g, 7);
			assert!(r.ok, "N = {n}");
		}
	}
    #[test]
    fn packed_open_uses_preprocessed_coefficients_and_original_linear_map() {
        let mut rng = StdRng::seed_from_u64(20261028);
        for n in [8,16,32,64,128,256] {
            let ctx = Ctx::new(n);
            // Arbitrary masked shares, including nonzero second-half shares.
            let shares: Vec<L> = (0..n).map(|_| L::random(&mut rng)).collect();
            let expected: Vec<L> = (0..ctx.k).map(|y|
                (0..n).map(|i| ctx.sharing.lagrange(i)[y]*shares[i]).sum()
            ).collect();
            crate::sharing::take_lagrange_calls();
            assert_eq!(ctx.open_packed(&shares),expected);
            assert_eq!(crate::sharing::take_lagrange_calls(),0,"online packed reconstruction regenerated public coefficients, N={n}");
        }
    }
    #[test]
    fn fixed_interp_matches_original_at_nodes_and_random_challenges() {
        let mut rng = StdRng::seed_from_u64(20261029);
        let w=from_b(omega()); let points=[L::ZERO,L::ONE,w,w+L::ONE];
        for len in 0..=4 {
            let vals: Vec<L>=(0..len).map(|_|L::random(&mut rng)).collect();
            for r in points.into_iter().chain((0..12).map(|_|L::random(&mut rng))) {
                let expected:L=lagrange_at(&points[..len],r).iter().zip(&vals).map(|(a,b)|*a**b).sum();
                assert_eq!(interp(&vals,r),expected);
            }
        }
    }

    #[test]
    fn preprocessed_fixed_interp_has_no_online_inverse_setup() {
        let _ctx=Ctx::new(8);
        LAGRANGE_AT_CALLS.with(|n|n.set(0));
        let values=[L::ONE,L::ZERO,from_b(omega()),L::ONE];
        let _ = interp(&values,from_b(omega())+L::ONE);
        assert_eq!(LAGRANGE_AT_CALLS.with(|n|n.get()),0,"fixed interpolation repeated public inverse setup online");
    }

	#[test]
	fn packed_open_matches_secrets_and_direct_interpolation() {
		let mut rng = StdRng::seed_from_u64(20261027);
		for n in [8, 16, 32, 64, 128] {
			let ctx = Ctx::new(n);
			for _ in 0..2 {
				let values: Vec<L> = (0..ctx.k).map(|_| L::random(&mut rng)).collect();
				let shares = ctx.share_packed(&values, &mut rng);
				assert_eq!(ctx.open_packed(&shares), values, "N={n}");
				// Even inconsistent inputs retain the original first-coset reconstruction.
				let arbitrary: Vec<L> = (0..n).map(|_| L::random(&mut rng)).collect();
				let coeffs = ctx.sharing.col.interpolate(&arbitrary[..ctx.kp], 1);
				let expected = ctx.sharing.col.evaluate(&coeffs)[..ctx.k].to_vec();
				assert_eq!(ctx.open_packed(&arbitrary), expected, "N={n}");
			}
		}
	}

}
