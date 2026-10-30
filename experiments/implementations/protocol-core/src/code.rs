//! Reed–Solomon codes over the novel polynomial basis, via the Binius64 additive NTT.
//!
//! * [`RowCode`]: FRI-Binius's row code Enc_j and its fold (the codeword fold of DP24 / Binius64
//!   `binius_iop::fri::fold::fold_pair`).
//! * [`ColCode`]: the column (party-direction) code used for packed Shamir sharing. Its domain is
//!   one Gao–Mateer subspace of size 4k' split into four cosets of size k'. Coset 0 holds the
//!   secret nodes η_0..η_{k'-1}; cosets 1 and 2 hold the N = 2k' party nodes ζ_1..ζ_N.
//!
//! Elements of L are processed as two B-coordinates, i.e. as a batch of two B-valued vectors
//! (`log_batch_size = 1`), exactly as Binius64 encodes extension-field data.

use binius_compute::GlobalAllocator;
use binius_math::{
	FieldSlice, FieldSliceMut, ReedSolomonCode,
	bit_reverse::reverse_bits,
	ntt::{
		AdditiveNTT, NeighborsLastReference, NeighborsLastSingleThread,
		domain_context::{GaoMateerPreExpanded, GaoMateerOnTheFly},
	},
};

use crate::field::{B, Field, L, mul_b};

type Dc = GaoMateerPreExpanded<B>;

fn as_b(v: &[L]) -> &[B] {
	bytemuck::cast_slice(v)
}

fn into_l(v: Vec<B>) -> Vec<L> {
	// L is 32-byte aligned, so a B buffer cannot be reinterpreted in place.
	v.chunks_exact(2).map(|p| bytemuck::cast::<[B; 2], L>([p[0], p[1]])).collect()
}

fn log2_exact(n: usize) -> usize {
	assert!(n.is_power_of_two(), "length {n} is not a power of two");
	n.trailing_zeros() as usize
}

/// Splits L-values into their two B-coordinate vectors, concatenated: Binius64's batched encoder
/// takes the batch index as the high bit of the input and returns it as the low bit of the output.
fn split_coords(msg: &[L]) -> Vec<B> {
	let mut out = vec![B::ZERO; 2 * msg.len()];
	let (lo, hi) = out.split_at_mut(msg.len());
	for (i, x) in msg.iter().enumerate() {
		let [a, b] = crate::field::coords(*x);
		lo[i] = a;
		hi[i] = b;
	}
	out
}

fn join_coords(v: &[B]) -> Vec<L> {
	let (lo, hi) = v.split_at(v.len() / 2);
	lo.iter().zip(hi).map(|(a, b)| bytemuck::cast::<[B; 2], L>([*a, *b])).collect()
}

/// Encodes `msg` (natural coefficient order) at rate 2^-log_inv_rate with the given NTT.
fn rs_encode<N: AdditiveNTT<Field = B> + Sync>(ntt: &N, msg: &[L], log_inv_rate: usize) -> Vec<L> {
	let lg = log2_exact(msg.len());
	let code = ReedSolomonCode::<B>::new(lg, log_inv_rate);
	let input = split_coords(msg);
	let out = code.encode_batch(ntt, FieldSlice::from_slice(lg + 1, &input), 1, &GlobalAllocator);
	into_l(out.as_ref().to_vec())
}

/// The row code: messages of length 2^ell, codewords of length 2^m with m = ell + beta.
pub struct RowCode {
	pub log_inv_rate: usize,
	pub log_domain: usize,
	ntt: Option<NeighborsLastSingleThread<Dc>>,
 compact: Option<GaoMateerOnTheFly<B>>,
}

impl RowCode {
	pub fn new(log_dim: usize, log_inv_rate: usize) -> Self {
		let log_domain = log_dim + log_inv_rate;
		let ntt = NeighborsLastSingleThread::new(Dc::generate(log_domain));
		Self { log_inv_rate, log_domain, ntt:Some(ntt), compact:None }
	}

	/// O(log domain) storage; only queried twiddles are evaluated.
 pub fn compact(log_dim:usize, log_inv_rate:usize)->Self {
  let log_domain=log_dim+log_inv_rate;
  Self{log_inv_rate,log_domain,ntt:None,compact:Some(GaoMateerOnTheFly::generate(log_domain))}
 }

	/// Enc_j for a message of length 2^(ell - j): the codeword has length 2^(m - j).
	///
	/// Binius64's codeword fold binds the most significant bit of the message index, while the
	/// paper's Fold_r binds the least significant bit of the column index. Handing the message to
	/// Binius64 in bit-reversed order makes the two agree: `fold(encode(a), r) ==
	/// encode(fold_coeffs(a, r))`, and the pair sum of a fibre depends only on odd coefficients.
	pub fn encode(&self, msg: &[L]) -> Vec<L> {
		let bits = log2_exact(msg.len());
		let reversed: Vec<L> = (0..msg.len()).map(|i| msg[reverse_bits(i, bits as u32)]).collect();
		match &self.ntt { Some(ntt)=>rs_encode(ntt,&reversed,self.log_inv_rate), None=>rs_encode(&NeighborsLastReference{domain_context:self.compact.as_ref().unwrap()},&reversed,self.log_inv_rate) }
	}

	/// Twiddle of the fibre `index` in a codeword of length 2^log_len.
	#[inline]
	pub fn twiddle(&self, log_len: usize, index: usize) -> B {
		match &self.ntt {Some(ntt)=>ntt.twiddle(log_len-1,index),None=>{use binius_math::ntt::DomainContext; self.compact.as_ref().unwrap().twiddle(log_len-1,index)}}
	}

	/// The inverse butterfly of a fibre: returns (A, B) with A the even part and B the pair sum.
	#[inline]
	pub fn unfold_pair(&self, log_len: usize, index: usize, u: L, v: L) -> (L, L) {
		let t = self.twiddle(log_len, index);
		let s = v + u;
		(u + mul_b(s, t), s)
	}

	/// FRI fold of one fibre with challenge r: (1 - r)·A + r·(A + B) in the coefficient view.
	#[inline]
	pub fn fold_pair(&self, log_len: usize, index: usize, u: L, v: L, r: L) -> L {
		let (a, s) = self.unfold_pair(log_len, index, u, v);
		// Binius64: u += v·t after v += u, then extrapolate_line(u, v, r) = u + (v - u)·r.
		a + (s - a) * r
	}

	/// Folds a whole codeword of length 2^log_len into one of length 2^(log_len - 1).
	pub fn fold(&self, cw: &[L], r: L) -> Vec<L> {
		let log_len = log2_exact(cw.len());
        let mut out=vec![L::ZERO;cw.len()/2];
        let mut chunks:Vec<_>=out.chunks_mut(4096).collect();
        crate::parallel::map_mut(&mut chunks, |c,out|{for(j,v)in out.iter_mut().enumerate(){let i=c*4096+j;*v=self.fold_pair(log_len,i,cw[2*i],cw[2*i+1],r);}});
        out
	}
}

/// Coefficient fold: Fold_r(a)(u) = (1 - r)·a(2u) + r·a(2u + 1).
pub fn fold_coeffs(a: &[L], r: L) -> Vec<L> {
    let mut out=vec![L::ZERO;a.len()/2];let mut chunks:Vec<_>=out.chunks_mut(4096).collect();
    crate::parallel::map_mut(&mut chunks, |c,out|{for(j,v)in out.iter_mut().enumerate(){let i=c*4096+j;*v=a[2*i]+(a[2*i+1]-a[2*i])*r;}});out
}

/// The column code for packed Shamir sharing with degree bound k' = 2^log_kp and N = 2k' parties.
pub struct ColCode {
	pub log_kp: usize,
	dc: Dc,
}

impl ColCode {
	pub fn new(log_kp: usize) -> Self {
		Self { log_kp, dc: Dc::generate(log_kp + 2) }
	}

	pub fn kp(&self) -> usize {
		1 << self.log_kp
	}

	fn ntt(&self) -> NeighborsLastReference<&Dc> {
		NeighborsLastReference { domain_context: &self.dc }
	}

	/// Evaluations of the polynomial with novel-basis coefficients `coeffs` (length k') on the
	/// whole domain: coset c occupies positions [c·k', (c+1)·k').
	pub fn evaluate(&self, coeffs: &[L]) -> Vec<L> {
		assert_eq!(coeffs.len(), self.kp());
		rs_encode(&self.ntt(), coeffs, 2)
	}

	/// Coefficients of the polynomial of degree < k' with the given values on coset `c`.
	pub fn interpolate(&self, values: &[L], c: usize) -> Vec<L> {
		let kp = self.kp();
		assert_eq!(values.len(), kp);
		let log_total = self.log_kp + 2 + 1; // domain bits + batch bit
		let mut buf = vec![B::ZERO; 1 << log_total];
		buf[2 * c * kp..2 * (c + 1) * kp].copy_from_slice(as_b(values));
		self.ntt()
			.inverse_transform(FieldSliceMut::from_slice(log_total, &mut buf), 2, 1);
		// The chunk now holds the bit-reversed message, as laid out by `encode_batch`.
		let chunk = &buf[2 * c * kp..2 * (c + 1) * kp];
		let bits = self.log_kp as u32 + 1;
		let msg: Vec<B> = (0..2 * kp).map(|i| chunk[reverse_bits(i, bits)]).collect();
		join_coords(&msg)
	}
}

#[cfg(test)]
mod tests {
	use rand::{SeedableRng, rngs::StdRng};

	use super::*;
	use crate::field::Random;

	fn rand_vec(rng: &mut StdRng, n: usize) -> Vec<L> {
		(0..n).map(|_| L::random(&mut *rng)).collect()
	}

	#[test]
	fn extension_encoding_is_coordinatewise() {
		// Encoding L-data equals encoding each B-coordinate separately.
		let mut rng = StdRng::seed_from_u64(10);
		let code = RowCode::new(6, 2);
		let msg = rand_vec(&mut rng, 64);
		let cw = rs_encode(code.ntt.as_ref().unwrap(), &msg, 2);
		for coord in 0..2 {
			let part: Vec<B> = msg.iter().map(|x| crate::field::coords(*x)[coord]).collect();
			let rs = ReedSolomonCode::<B>::new(6, 2);
			let enc = rs.encode_batch(code.ntt.as_ref().unwrap(), FieldSlice::from_slice(6, &part), 0, &GlobalAllocator);
			let want: Vec<B> = enc.as_ref().to_vec();
			let got: Vec<B> = cw.iter().map(|x| crate::field::coords(*x)[coord]).collect();
			assert_eq!(got, want, "coordinate {coord}");
		}
	}

	#[test]
	fn fold_commutes_with_encoding() {
		let mut rng = StdRng::seed_from_u64(11);
		let code = RowCode::new(7, 2);
		let mut msg = rand_vec(&mut rng, 128);
		let mut cw = code.encode(&msg);
		for _ in 0..4 {
			let r = L::random(&mut rng);
			cw = code.fold(&cw, r);
			msg = fold_coeffs(&msg, r);
			assert_eq!(cw, code.encode(&msg));
		}
	}

	#[test]
	fn pair_sum_is_the_odd_part() {
		// The B-component of the inverse butterfly is the fold's slope: fold at r=0 gives A,
		// at r=1 gives B; A and B are encodings of the even/odd coefficient halves.
		let mut rng = StdRng::seed_from_u64(12);
		let code = RowCode::new(5, 2);
		let msg = rand_vec(&mut rng, 32);
		let cw = code.encode(&msg);
		let even: Vec<L> = msg.iter().step_by(2).copied().collect();
		let odd: Vec<L> = msg.iter().skip(1).step_by(2).copied().collect();
		assert_eq!(code.fold(&cw, L::ZERO), code.encode(&even));
		assert_eq!(code.fold(&cw, L::ONE), code.encode(&odd));
	}

	#[test]
	fn column_code_interpolates_from_any_coset() {
		let mut rng = StdRng::seed_from_u64(13);
		let col = ColCode::new(4);
		let coeffs = rand_vec(&mut rng, 16);
		let evals = col.evaluate(&coeffs);
		for c in 0..4 {
			let back = col.interpolate(&evals[16 * c..16 * (c + 1)], c);
			assert_eq!(back, coeffs, "coset {c}");
		}
	}
}


