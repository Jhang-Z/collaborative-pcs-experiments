//! Public setup, instances, and the public mask weight M_ω.

use std::collections::HashMap;

use rand::{SeedableRng, rngs::StdRng};

use crate::{
	algebra::chi_map,
	code::RowCode,
	field::{Field, L, Random, eq_expand, from_words},
	params::{Layout, Params},
	sharing::Sharing,
};

/// The fixed chain weight c_ch ∉ {0, 1}.
pub fn c_ch() -> L {
	from_words([2, 0])
}

pub struct Setup {
	pub params: Params,
	pub layout: Layout,
	pub row: RowCode,
	pub sharing: Sharing,
	/// Λ_{i,y} for every party (public, reusable across openings).
	pub lagrange: Vec<Vec<L>>,
    mask_template: Vec<(usize,L)>,
    mask_updates: Vec<(usize,usize)>,
}

fn prepare_mask_plan(layout:&Layout)->(Vec<(usize,L)>,Vec<(usize,usize)>) {
    let mut weights:HashMap<usize,L>=HashMap::new();
    for &(x,is_ch) in &layout.chain {*weights.entry(x).or_insert(L::ZERO)+=if is_ch {c_ch()} else {L::ONE};}
    for pos in &layout.omega_pos {for &x in pos {weights.entry(x).or_insert(L::ZERO);}}
    let mut template:Vec<_>=weights.into_iter().collect();template.sort_unstable_by_key(|x|x.0);
    let mut updates=Vec::new();
    for (c,pos) in layout.omega_pos.iter().enumerate() {for (j,&x) in pos.iter().enumerate() {
        updates.push((3*c+j,template.binary_search_by_key(&x,|x|x.0).unwrap()));
    }}
    (template,updates)
}

impl Setup {
	pub fn new(params: Params) -> Self {
		let layout = Layout::new(&params);
		let row = RowCode::new(params.ell, params.beta);
		let sharing = Sharing::new(params.n_parties);
		let lagrange = (0..params.n_parties).map(|i| sharing.lagrange(i)).collect();
		let (mask_template,mask_updates)=prepare_mask_plan(&layout);
        Self { params, layout, row, sharing, lagrange, mask_template,mask_updates }
	}

 /// Verifier-only construction: no full row NTT, ownership list, or bit-address table.
 pub fn verifier(params:Params)->Self {
  let layout=Layout::verifier(&params);
  let row=RowCode::compact(params.ell,params.beta);
  let sharing=Sharing::new(params.n_parties);
  let lagrange=(0..params.n_parties).map(|i|sharing.lagrange(i)).collect();
  let (mask_template,mask_updates)=prepare_mask_plan(&layout);
  Self{params,layout,row,sharing,lagrange,mask_template,mask_updates}
 }
	pub fn log_k(&self) -> usize {
		self.params.k().trailing_zeros() as usize
	}

	/// The public mask weight M_ω as (column, weight) pairs on logical row 0.
    pub fn mask_weight(&self,omega:&[L])->Vec<(usize,L)> {
        let mut out=self.mask_template.clone();
        for &(source,target) in &self.mask_updates {out[target].1+=omega[source];}
        out
    }
    pub(crate) fn mask_cache_payload_bytes(&self)->usize {
        self.mask_template.len()*std::mem::size_of::<(usize,L)>()
        +self.mask_updates.len()*std::mem::size_of::<(usize,usize)>()
    }

	pub fn n_omega(&self) -> usize {
		3 * self.layout.omega_pos.len()
	}
}

/// The evaluation claim: point r = (r_H, r_A, r_B) and value s_x = B~(r).
#[derive(Clone)]
pub struct Instance {
	pub r_h: Vec<L>,
	pub r_a: Vec<L>,
	pub r_b: Vec<L>,
	pub s_x: L,
}

impl Instance {
	pub fn to_bytes(&self) -> Vec<u8> {
		let all: Vec<L> = self.r_h.iter().chain(&self.r_a).chain(&self.r_b).copied().chain([self.s_x]).collect();
		bytemuck::cast_slice(&all).to_vec()
	}
}

/// The logical table X (k × n, row-major). Padding columns are unused (their logical values are
/// never known to anyone); data entries and tensor masks are random.
pub struct Witness {
	pub table: Vec<L>,
}

impl Witness {
	pub fn get(&self, n: usize, y: usize, x: usize) -> L {
		self.table[y * n + x]
	}
}

/// The evaluation point r = (r_H, r_A, r_B), derived from a seed (shared by all processes).
pub fn instance_point(setup: &Setup, seed: u64) -> (Vec<L>, Vec<L>, Vec<L>) {
	let mut rng = StdRng::seed_from_u64(seed ^ 0x9017);
	let mut rand_vec = |len: usize| (0..len).map(|_| L::random(&mut rng)).collect::<Vec<L>>();
	let r_h = rand_vec(crate::field::LOG_D);
	let r_a = rand_vec(setup.log_k());
	let r_b = rand_vec(setup.params.ell);
	(r_h, r_a, r_b)
}

/// Number of data entries owned by parties before `p`.
fn data_offset(setup: &Setup, p: usize) -> usize {
	let k = setup.params.k();
	setup.layout.owned[..p].iter().enumerate().map(|(i,c)| c.len() * k - setup.layout.masks[i].len()).sum()
}

/// Fills owner p's entries of the logical table: its tensor masks are random, and its data
/// entries are random up to the global budget `n_data` (entries ordered by owner, column, row);
/// the rest of the capacity stays zero. Values depend only on (seed, p).
pub fn fill_owner(setup: &Setup, table: &mut [L], p: usize, seed: u64, n_data: Option<usize>) {
	let (n, k) = (setup.params.n(), setup.params.k());
	let mut rng = StdRng::seed_from_u64(seed ^ ((p as u64 + 1) << 24));
	let mut left = n_data.map_or(usize::MAX, |b| b.saturating_sub(data_offset(setup, p)));
	for &x in &setup.layout.owned[p] {
		for y in 0..k {
			if setup.layout.mask_index(p, y, x).is_some() {
				table[y * n + x] = L::random(&mut rng);
			} else if left > 0 {
				table[y * n + x] = L::random(&mut rng);
				left -= 1;
			}
		}
	}
}

/// Owner p's part of s_x = λ_r(S_X) = Σ_{data} χ_y(r_A) χ_x(r_B) ψ_{r_H}(X(y, x)).
pub fn partial_claim(setup: &Setup, p: usize, table: &[L], point: &(Vec<L>, Vec<L>, Vec<L>)) -> L {
	let (n, k) = (setup.params.n(), setup.params.k());
	let psi = chi_map(&point.0);
	let ea = eq_expand(&point.1);
	let mut s = L::ZERO;
	for &x in &setup.layout.owned[p] {
		let bx = crate::field::chi(x, &point.2);
		for y in 0..k {
			if setup.layout.mask_index(p, y, x).is_none() {
				s += ea[y] * bx * psi.apply(table[y * n + x]);
			}
		}
	}
	s
}

/// A random witness and evaluation point with its true claim (all owners in one process).
pub fn random_instance(setup: &Setup, seed: u64, n_data: Option<usize>) -> (Instance, Witness) {
	let (n, k) = (setup.params.n(), setup.params.k());
	let mut table = vec![L::ZERO; k * n];
	let point = instance_point(setup, seed);
	let mut s_x = L::ZERO;
	for p in 0..setup.params.n_parties {
		fill_owner(setup, &mut table, p, seed, n_data);
		s_x += partial_claim(setup, p, &table, &point);
	}
	let (r_h, r_a, r_b) = point;
	(Instance { r_h, r_a, r_b, s_x }, Witness { table })
}

#[cfg(test)]
mod precompute_tests {
    use super::*;
    #[test]
    fn cached_mask_plan_preserves_duplicates_zero_values_and_compact_setup() {
        let mut rng=StdRng::seed_from_u64(20261032);
        for n in [8,16,64,256] {
            let params=Params{n_parties:n,ell:12,beta:2,gamma:16,tau:3,salt_bytes:32};
            for setup in [Setup::new(params.clone()),Setup::verifier(params)] {
                for random in [false,true,true] {
                    let omega:Vec<L>=(0..setup.n_omega()).map(|_|if random {L::random(&mut rng)} else {L::ZERO}).collect();
                    let mut expected:HashMap<usize,L>=HashMap::new();
                    for &(x,is_ch) in &setup.layout.chain {*expected.entry(x).or_insert(L::ZERO)+=if is_ch {c_ch()} else {L::ONE};}
                    for (c,pos) in setup.layout.omega_pos.iter().enumerate() {for (j,&x) in pos.iter().enumerate() {*expected.entry(x).or_insert(L::ZERO)+=omega[3*c+j];}}
                    let mut expected:Vec<_>=expected.into_iter().collect();expected.sort_unstable_by_key(|x|x.0);
                    assert_eq!(setup.mask_weight(&omega),expected);
                }
            }
        }
    }
}
