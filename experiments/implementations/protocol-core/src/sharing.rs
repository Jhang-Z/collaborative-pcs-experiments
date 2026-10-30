//! Packed Shamir sharing along columns (Section 4.3) on the column code of [`ColCode`]:
//! secrets at the first k nodes of coset 0 (η_y), party i at position k' + i (cosets 1 and 2).

use rand::Rng;

use crate::{
	code::ColCode,
	field::{Field, L, Random},
};

#[cfg(test)]
std::thread_local! { static LAGRANGE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
#[cfg(test)]
pub(crate) fn take_lagrange_calls() -> usize { LAGRANGE_CALLS.with(|n| n.replace(0)) }

pub struct Sharing {
	pub col: ColCode,
	pub n_parties: usize,
	pub k: usize,
}

impl Sharing {
	pub fn new(n_parties: usize) -> Self {
		let log_kp = n_parties.trailing_zeros() as usize - 1;
		Self { col: ColCode::new(log_kp), n_parties, k: n_parties / 4 }
	}

	fn kp(&self) -> usize {
		self.col.kp()
	}

	/// Shares of a column with logical values `values` (length k): the owner samples the
	/// remaining k' - k values on coset 0 uniformly.
	pub fn share(&self, values: &[L], rng: &mut impl Rng) -> Vec<L> {
		assert_eq!(values.len(), self.k);
		let kp = self.kp();
		let mut coset0 = values.to_vec();
		coset0.extend((self.k..kp).map(|_| L::random(&mut *rng)));
		let coeffs = self.col.interpolate(&coset0, 0);
		self.col.evaluate(&coeffs)[kp..3 * kp].to_vec()
	}

	/// Shares of a uniformly random column polynomial (the ideal functionality F_rand).
	pub fn random_shares(&self, rng: &mut impl Rng) -> Vec<L> {
		let kp = self.kp();
		let coeffs: Vec<L> = (0..kp).map(|_| L::random(&mut *rng)).collect();
		self.col.evaluate(&coeffs)[kp..3 * kp].to_vec()
	}

	/// Lagrange coefficients Λ_{i,y} (y < k) with P(η_y) = Σ_i Λ_{i,y} P(ζ_i). We reconstruct from
	/// the k' parties on coset 1, so Λ_{i,·} = 0 for the parties on coset 2.
	pub fn lagrange(&self, i: usize) -> Vec<L> {
        #[cfg(test)] LAGRANGE_CALLS.with(|n| n.set(n.get()+1));
		let kp = self.kp();
		if i >= kp {
			return vec![L::ZERO; self.k];
		}
		let mut e = vec![L::ZERO; kp];
		e[i] = L::ONE;
		let coeffs = self.col.interpolate(&e, 1);
		self.col.evaluate(&coeffs)[..self.k].to_vec()
	}

	/// Column decoding (check (d)): returns the k logical values if the N shares lie on a
	/// polynomial of degree < k', and `None` otherwise.
	pub fn decode(&self, shares: &[L]) -> Option<Vec<L>> {
		let kp = self.kp();
		assert_eq!(shares.len(), 2 * kp);
		let coeffs = self.col.interpolate(&shares[..kp], 1);
		let evals = self.col.evaluate(&coeffs);
		(evals[2 * kp..3 * kp] == shares[kp..]).then(|| evals[..self.k].to_vec())
	}
}

#[cfg(test)]
mod tests {
	use rand::{SeedableRng, rngs::StdRng};

	use super::*;

	#[test]
	fn share_reconstruct_and_decode() {
		let mut rng = StdRng::seed_from_u64(30);
		let s = Sharing::new(16);
		let values: Vec<L> = (0..4).map(|_| L::random(&mut rng)).collect();
		let shares = s.share(&values, &mut rng);
		assert_eq!(s.decode(&shares), Some(values.clone()));
		for y in 0..4 {
			let rec: L = (0..16).map(|i| s.lagrange(i)[y] * shares[i]).sum();
			assert_eq!(rec, values[y]);
		}
		let mut bad = shares.clone();
		bad[12] += L::ONE;
		assert_eq!(s.decode(&bad), None);
	}
}
