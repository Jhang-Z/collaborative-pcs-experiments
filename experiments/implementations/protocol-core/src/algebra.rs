//! F2-linear maps on L and the tensor algebra L ⊗_{F2} L used by Ring Switching (Section 3).

use crate::field::{D, Field, L, basis, bit, eq_expand, to_words};

/// An F2-linear map L → L given by the images of the basis β_u, evaluated with the method of
/// four Russians: 32 tables of 256 entries, one per byte of the input.
pub struct LinearMap {
	tables: Vec<[L; 256]>,
}

impl LinearMap {
	pub fn new(images: &[L]) -> Self {
		assert_eq!(images.len(), D);
		let tables = images
			.chunks_exact(8)
			.map(|img| {
				let mut t = [L::ZERO; 256];
				for byte in 1..256usize {
					let low = byte & byte.wrapping_neg();
					t[byte] = t[byte ^ low] + img[low.trailing_zeros() as usize];
				}
				t
			})
			.collect();
		Self { tables }
	}

	/// Σ_u [a]_u · images[u].
	#[inline]
	pub fn apply(&self, a: L) -> L {
		let bytes: [u8; 32] = bytemuck::cast(to_words(a));
		let mut acc = L::ZERO;
		for (t, &b) in self.tables.iter().zip(&bytes) {
			acc += t[b as usize];
		}
		acc
	}
}

/// The map a ↦ Σ_u [a]_u χ_u(z) for z ∈ L^8: ψ_{r_H} and φ_{r''} of the paper.
pub fn chi_map(z: &[L]) -> LinearMap {
	assert_eq!(1 << z.len(), D);
	LinearMap::new(&eq_expand(z))
}

/// An element of L ⊗ L in the left-L-module basis {1 ⊗ β_v}: Σ_v coords[v] ⊗ β_v.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tensor {
	pub coords: Vec<L>,
}

impl Tensor {
	/// 1 ⊗ 1, i.e. coords[v] = [1]_v.
	pub fn one() -> Self {
		let coords = (0..D).map(|v| if bit(L::ONE, v) { L::ONE } else { L::ZERO }).collect();
		Self { coords }
	}

	/// Right-multiplies by Σ_j (a_j ⊗ b_j).
	pub fn mul_simple_sum(&self, terms: &[(L, L)]) -> Self {
		let mut out = vec![L::ZERO; D];
		for &(a, b) in terms {
			for v in 0..D {
				let az = a * self.coords[v];
				let img = basis(v) * b; // β_v · b, expanded in the basis
				let w = to_words(img);
				for (half, &word) in w.iter().enumerate() {
					let mut word = word;
					while word != 0 {
						let tz = word.trailing_zeros() as usize;
						out[128 * half + tz] += az;
						word &= word - 1;
					}
				}
			}
		}
		Self { coords: out }
	}

	/// Coordinates of self · (1 ⊗ c).
	pub fn mul_right(&self, c: L) -> Vec<L> {
		self.mul_simple_sum(&[(L::ONE, c)]).coords
	}
}

/// Bits of x as an iterator of indices u with [x]_u = 1.
pub fn bits_of(x: L) -> impl Iterator<Item = usize> {
	(0..D).filter(move |&u| bit(x, u))
}

#[cfg(test)]
mod tests {
	use rand::{SeedableRng, rngs::StdRng};

	use super::*;
	use crate::field::Random;

	#[test]
	fn linear_map_matches_bit_sum() {
		let mut rng = StdRng::seed_from_u64(40);
		let images: Vec<L> = (0..D).map(|_| L::random(&mut rng)).collect();
		let m = LinearMap::new(&images);
		let a = L::random(&mut rng);
		let want: L = bits_of(a).map(|u| images[u]).sum();
		assert_eq!(m.apply(a), want);
	}

	#[test]
	fn tensor_product_identity() {
		// Σ_x χ_x(r) ⊗ χ_x(ρ) equals Π_t ((1 - r_t) ⊗ (1 - ρ_t) + r_t ⊗ ρ_t).
		let mut rng = StdRng::seed_from_u64(41);
		let r: Vec<L> = (0..3).map(|_| L::random(&mut rng)).collect();
		let rho: Vec<L> = (0..3).map(|_| L::random(&mut rng)).collect();
		let mut e = Tensor::one();
		for t in 0..3 {
			e = e.mul_simple_sum(&[(L::ONE - r[t], L::ONE - rho[t]), (r[t], rho[t])]);
		}
		let (cr, crho) = (eq_expand(&r), eq_expand(&rho));
		let mut direct = Tensor { coords: vec![L::ZERO; D] };
		for x in 0..8 {
			let t = Tensor::one().mul_simple_sum(&[(cr[x], crho[x])]);
			for v in 0..D {
				direct.coords[v] += t.coords[v];
			}
		}
		assert_eq!(e, direct);
	}
}
