//! Parameters and the table layout of Section 4.1–4.2 of the paper.

use std::collections::HashSet;

use crate::field::{D, LOG_D};

/// Bound into both transcript modes; old per-block-mask proofs are incompatible.
pub const LAYOUT_ID: &[u8] = b"global-d-capacity-v2";

#[derive(Clone, Debug)]
pub struct Params {
	/// Number of parties N (a power of two, N ≥ 4); k = N/4, k' = N/2.
	pub n_parties: usize,
	/// ℓ: a share-row has n = 2^ℓ columns.
	pub ell: usize,
	/// β: the row code has rate 2^-β, codeword length 2^m with m = ℓ + β.
	pub beta: usize,
	/// γ: number of query repetitions.
	pub gamma: usize,
	/// τ: the tail has length 2^τ; the protocol folds ℓ - τ times.
	pub tau: usize,
	/// Leaf salt length in bytes.
	pub salt_bytes: usize,
}

impl Params {
	pub fn k(&self) -> usize {
		self.n_parties / 4
	}
	pub fn kp(&self) -> usize {
		self.n_parties / 2
	}
	pub fn log_n_parties(&self) -> usize {
		self.n_parties.trailing_zeros() as usize
	}
	pub fn n(&self) -> usize {
		1 << self.ell
	}
	pub fn m(&self) -> usize {
		self.ell + self.beta
	}
	/// Number of folding rounds ℓ - τ.
	pub fn folds(&self) -> usize {
		self.ell - self.tau
	}
	/// Number of rounds μ = ℓ - τ + 4 of the compiled protocol.
	pub fn mu(&self) -> usize {
		self.folds() + 4
	}
	/// Masking depth c* = ℓ - ⌈log2(γ + 2)⌉.
	pub fn cstar(&self) -> usize {
		self.ell - ceil_log2(self.gamma + 2)
	}
	/// Fibres per row on layer j: F_j = 2^(m - j - 1).
	pub fn fibres(&self, j: usize) -> usize {
		1 << (self.m() - j - 1)
	}

	pub fn validate(&self) {
		assert_eq!(self.salt_bytes,32,"this implementation uses 256-bit leaf salts");
		let n = self.n_parties;
		assert!(n.is_power_of_two() && n >= 4, "N must be a power of two ≥ 4");
		assert!(self.gamma >= 4);
		let lg = ceil_log2(self.gamma + 2);
		assert!(self.ell > lg, "need c* ≥ 1");
		assert!(3 <= self.tau && self.tau < lg, "need 3 ≤ τ < ⌈log2(γ+2)⌉");
		assert!(self.m() + 1 <= 128, "row domain must fit the 128-bit subfield");
	}
}

pub fn ceil_log2(x: usize) -> usize {
	(usize::BITS - (x - 1).leading_zeros()) as usize
}

/// A table entry (y, x): logical row y < k, column x < n.
pub type Entry = (usize, usize);

/// One global tensor mask θ = (y_θ, x_θ, h_θ); all parties hold its shares.
#[derive(Clone, Copy, Debug)]
pub struct Mask {
	pub y: usize,
	pub x: usize,
	pub h: usize,
}

/// The table layout: padding columns, ownership blocks, tensor masks, data entries, and the
/// support of the public mask weight M_ω.
#[derive(Clone, Debug)]
pub struct Layout {
	pub n: usize,
	pub k: usize,
	/// Padding columns, sorted.
	pub pad: Vec<usize>,
	pub is_pad: Vec<bool>,
	/// Owned (non-padding) columns of each party, sorted.
	pub owned: Vec<Vec<usize>>,
	/// Global d masks, grouped by their public ownership labels.
	pub masks: Vec<Vec<Mask>>,
	/// Chain positions with their fixed weights (index into `chain_weight_kind`: 0 → 1, 1 → c_ch).
	pub chain: Vec<(usize, bool)>,
	/// For each layer c < c*, the three positions (a_c, b_c, t_c) carrying ω challenges.
	pub omega_pos: Vec<[usize; 3]>,
}

impl Layout {
	pub fn new(p: &Params) -> Self { Self::build(p,false) }
 /// No table-sized allocation or scan. Prover-only ownership arrays are empty.
 pub fn verifier(p:&Params)->Self { Self::build(p,true) }
 fn build(p:&Params,compact:bool)->Self {
		p.validate();
		let (n, k, gamma, cstar, ell) = (p.n(), p.k(), p.gamma, p.cstar(), p.ell);

		// Pad = ∪_{c<c*} {2^c + h·2^(c+1) : h < γ+2} ∪ {v·2^c* : v < 2^(ℓ-c*)}.
		let mut pad_set = HashSet::new();
		for c in 0..cstar {
			for h in 0..gamma + 2 {
				pad_set.insert((1 << c) + h * (1 << (c + 1)));
			}
		}
		for v in 0..1usize << (ell - cstar) {
			pad_set.insert(v << cstar);
		}
		let mut pad: Vec<usize> = pad_set.into_iter().collect();
		pad.sort_unstable();
		let mut is_pad = if compact {Vec::new()} else {vec![false;n]};
  if !compact {for &x in &pad {is_pad[x]=true;}}

		// Chain positions: {0} ∪ {2^s}_{s<ℓ} with weight 1, {3·2^s}_{s<ℓ-1} with weight c_ch.
		let mut chain = vec![(0, false)];
		chain.extend((0..ell).map(|s| (1 << s, false)));
		chain.extend((0..ell - 1).map(|s| (3 << s, true)));
		let chain_set: HashSet<usize> = chain.iter().map(|&(x, _)| x).collect();

		// ω positions per layer c < c*.
		let omega_pos = (0..cstar)
			.map(|c| {
				let a = (1 << c) + gamma * (1 << (c + 1));
				let b = (1 << c) + (gamma + 1) * (1 << (c + 1));
				let t = [gamma, gamma + 1]
					.into_iter()
					.map(|h| h << (c + 1))
					.find(|t| !chain_set.contains(t))
					.expect("one of the two candidates avoids the chain");
				[a, b, t]
			})
			.collect::<Vec<_>>();
		for c in &omega_pos {
			for &x in c {
				assert!(pad.binary_search(&x).is_ok(), "ω position {x} must be a padding column");
			}
		}

		// Ownership: non-padding columns split into N contiguous blocks.
		let free: Vec<usize> = if compact {vec![]} else {(0..n).filter(|&x| !is_pad[x]).collect()};
  let free_len=n-pad.len();
  let select=|rank:usize| {let(mut lo,mut hi)=(rank,n-1);while lo<hi {let mid=(lo+hi)/2;let count=mid+1-pad.partition_point(|&x|x<=mid);if count>rank {hi=mid;} else {lo=mid+1;}}lo};
		let n_parties = p.n_parties;
        let owned: Vec<Vec<usize>> = if compact { Vec::new() } else {
            (0..n_parties).map(|i| free[i*free_len/n_parties..(i+1)*free_len/n_parties].to_vec()).collect()
        };
        // One global basis-sized mask in the first nonpadding cells, column-major.
        // Ownership labels do not impose an additional per-block mask capacity.
        assert!(k * free_len >= D, "global table too small for tensor masks");
        let mut masks = vec![Vec::new(); n_parties];
        for h in 0..D {
            let rank = h / k;
            let owner = ((rank + 1) * n_parties - 1) / free_len;
            let x = if compact { select(rank) } else { free[rank] };
            masks[owner].push(Mask { y: h % k, x, h });
        }

		Self { n, k, pad, is_pad, owned:if compact {vec![]} else {owned}, masks, chain, omega_pos }
	}

	/// Number of data entries (each holds d = 256 input bits).
	pub fn n_data_entries(&self) -> usize {
		(self.n - self.pad.len()) * self.k - D
	}

    /// Whether this owner's cell is among the global d masks.
    pub fn mask_index(&self, owner: usize, y: usize, x: usize) -> Option<usize> {
        self.masks[owner].iter().find(|m| m.y == y && m.x == x).map(|m| m.h)
    }
}

/// Number of input bits that fit a layout: d per data entry.
pub fn input_bits(layout: &Layout) -> usize {
	layout.n_data_entries() << LOG_D
}

/// Smallest global-capacity lower bound; applications additionally check their maps.
pub fn ell_for_bits(n_parties: usize, gamma: usize, tau: usize, beta: usize, bits: usize) -> usize {
	(1..40)
		.find(|&ell| {
			let p = Params { n_parties, ell, beta, gamma, tau, salt_bytes: 32 };
			let lg = ceil_log2(gamma + 2);
			if ell <= lg {
				return false;
			}
			let pad = (ell - lg) * (gamma + 2) + (1 << lg);
			let free = (1usize << ell).saturating_sub(pad);
            p.k() * free >= D + bits.div_ceil(D)
		})
		.expect("no ℓ below 40 fits")
}

#[cfg(test)]
mod global_mask_tests {
    use super::*;

    #[test]
    fn global_capacity_small_owner_blocks_and_compact_layout() {
        for n in [8,16,32,64,128,256] {
            let p=Params{n_parties:n,ell:11,beta:2,gamma:871,tau:4,salt_bytes:32};
            let full=Layout::new(&p); let compact=Layout::verifier(&p);
            let masks=|l:&Layout|l.masks.iter().flatten().map(|m|(m.h,m.y,m.x)).collect::<Vec<_>>();
            assert_eq!(masks(&full),masks(&compact));
            assert_eq!(masks(&full).len(),D);
            let mut distinct=std::collections::HashSet::new();
            for (owner,ms) in full.masks.iter().enumerate() {for m in ms {
                assert!(distinct.insert((m.y,m.x)));
                assert!(!full.is_pad[m.x]); assert!(full.owned[owner].contains(&m.x));
                assert_eq!(full.mask_index(owner,m.y,m.x),Some(m.h));
            }}
        }
        for (n,ell) in [(32,13),(64,13),(128,12),(256,12)] {
            assert_eq!(ell_for_bits(n,871,4,2,64*131072),ell);
        }
    }

    #[test]
    fn global_mask_partition_matches_compact_verifier() {
        for n_parties in [4, 8, 16, 32] {
            let p = Params { n_parties, ell: 11, beta: 2, gamma: 14, tau: 3, salt_bytes: 32 };
            let full = Layout::new(&p);
            let compact = Layout::verifier(&p);
            let positions = |l: &Layout| l.masks.iter().flatten().map(|m| (m.y,m.x,m.h)).collect::<Vec<_>>();
            assert_eq!(positions(&full), positions(&compact));
            assert_eq!(positions(&full).len(), D);
            assert_eq!(full.n_data_entries(), compact.n_data_entries());
            let mut data = 0;
            for (owner, cols) in full.owned.iter().enumerate() {
                for &x in cols {
                    assert!(!full.is_pad[x]);
                    for y in 0..p.k() { data += usize::from(full.mask_index(owner,y,x).is_none()); }
                }
                if owner > 0 {
                    for h in 0..D { assert!(full.mask_index(owner,h%p.k(),cols[h/p.k()]).is_none()); }
                }
            }
            assert_eq!(data, full.n_data_entries());
            assert_eq!(data + D + p.k()*full.pad.len(), p.k()*p.n());
        }
    }
}
