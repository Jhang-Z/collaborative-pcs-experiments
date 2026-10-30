//! Field types and small helpers.
//!
//! The packing field is L = GF(2^256), taken from Binius64 as `GhashSq256b`: a degree-two
//! extension of the GHASH field `Ghash128b`. NTT twiddles and the sharing nodes live in the
//! 128-bit subfield B. An element of L is stored as two B coordinates `[a, b]` (meaning a + b·Y).
//! The F2-basis (β_u)_{u<256} used for bit packing is the bit basis of that 256-bit word:
//! u < 128 is bit u of `a`, u ≥ 128 is bit u−128 of `b`.

pub use binius_field::{Field, Ghash128b as B, GhashSq256b as L, Random};

/// Extension degree d = [L : F2].
pub const D: usize = 256;
pub const LOG_D: usize = 8;

#[inline]
pub fn to_words(x: L) -> [u128; 2] {
	bytemuck::cast(x)
}

#[inline]
pub fn from_words(w: [u128; 2]) -> L {
	bytemuck::cast(w)
}

/// The u-th F2-coordinate [x]_u.
#[inline]
pub fn bit(x: L, u: usize) -> bool {
	let w = to_words(x);
	(w[u >> 7] >> (u & 127)) & 1 == 1
}

/// The basis element β_u.
#[inline]
pub fn basis(u: usize) -> L {
	let mut w = [0u128; 2];
	w[u >> 7] = 1u128 << (u & 127);
	from_words(w)
}

/// Embeds the subfield B into L (the coefficient of 1).
#[inline]
pub fn from_b(x: B) -> L {
	from_words([bytemuck::cast(x), 0])
}

/// The two B-coordinates of x.
#[inline]
pub fn coords(x: L) -> [B; 2] {
	bytemuck::cast(x)
}

/// x · s for s in the subfield B (two B multiplications).
#[inline]
pub fn mul_b(x: L, s: B) -> L {
	let [a, b] = coords(x);
	bytemuck::cast([a * s, b * s])
}

/// Multilinear Lagrange basis χ_b(r) for all b < 2^len, with bit t of b paired with r[t]
/// (least-significant bit first).
pub fn eq_expand(r: &[L]) -> Vec<L> {
	let mut out = Vec::with_capacity(1 << r.len());
	out.push(L::ONE);
	for &rt in r {
		// r[t] becomes index bit t: the new half is the upper one.
		let n = out.len();
		out.resize(2 * n, L::ZERO);
		for i in 0..n {
			let v = out[i];
			let hi = v * rt;
			out[i + n] = hi;
			out[i] = v - hi;
		}
	}
	out
}

#[inline]
pub fn reverse_bits(x: usize, bits: usize) -> usize {
	if bits == 0 { 0 } else { x.reverse_bits() >> (usize::BITS as usize - bits) }
}

/// χ_b(r) for a single index b.
pub fn chi(b: usize, r: &[L]) -> L {
	r.iter()
		.enumerate()
		.map(|(t, &rt)| if (b >> t) & 1 == 1 { rt } else { L::ONE - rt })
		.product()
}

#[cfg(test)]
mod tests {
	use rand::{SeedableRng, rngs::StdRng};

	use super::*;

	#[test]
	fn words_and_bits_roundtrip() {
		let mut rng = StdRng::seed_from_u64(1);
		let x = L::random(&mut rng);
		let mut y = L::ZERO;
		for u in 0..D {
			if bit(x, u) {
				y += basis(u);
			}
		}
		assert_eq!(x, y);
	}

	#[test]
	fn subfield_embedding_is_a_ring_map() {
		let mut rng = StdRng::seed_from_u64(2);
		let (s, t) = (B::random(&mut rng), B::random(&mut rng));
		assert_eq!(from_b(s) * from_b(t), from_b(s * t));
		let x = L::random(&mut rng);
		assert_eq!(mul_b(x, s), x * from_b(s));
	}

	#[test]
	fn eq_expand_matches_chi() {
		let mut rng = StdRng::seed_from_u64(3);
		let r: Vec<L> = (0..5).map(|_| L::random(&mut rng)).collect();
		let e = eq_expand(&r);
		for b in 0..32 {
			assert_eq!(e[b], chi(b, &r));
		}
		assert_eq!(e.iter().copied().sum::<L>(), L::ONE);
	}
}
