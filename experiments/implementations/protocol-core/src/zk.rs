//! v0.4 numerical masks and the padded arbitrary-L weighted Fold backend.
use crate::spartan::omega;
use crate::{
    field::{Field, L, Random, chi},
    fs::Transcript,
    merkle::{Hasher, Tree},
    protocol::{self, Prepared, Proof, TAG_TAIL},
    setup::{Setup, Witness},
};
use binius_hash::Blake3HashSuite as H;
use rand::Rng;

pub const BIT_ROLE: u64 = 1;
pub const G_ROLE: u64 = 2;
#[derive(Clone)]
pub struct Selector {
    pub polys: Vec<Vec<L>>,
}
impl Selector {
    pub fn random(len: usize, degree: usize, rng: &mut impl Rng) -> Self {
        Self {
            polys: (0..len)
                .map(|_| (0..=degree).map(|_| L::random(&mut *rng)).collect())
                .collect(),
        }
    }
    pub fn sum(&self) -> L {
        self.polys
            .iter()
            .map(|c| c.iter().skip(1).copied().sum::<L>())
            .sum()
    }
    pub fn eval_poly(c: &[L], x: L) -> L {
        c.iter().rev().fold(L::ZERO, |a, &v| a * x + v)
    }
    pub fn round(&self, prefix: &[L]) -> Vec<L> {
        let i = prefix.len();
        let c: L = prefix.iter().map(|&r| L::ONE + r).product();
        let past: L = prefix
            .iter()
            .enumerate()
            .map(|(j, &r)| {
                Self::eval_poly(&self.polys[j], r)
                    * prefix
                        .iter()
                        .enumerate()
                        .filter(|&(h, _)| h != j)
                        .map(|(_, &r)| L::ONE + r)
                        .product::<L>()
            })
            .sum();
        let future: L = self.polys[i + 1..]
            .iter()
            .map(|v| v.iter().skip(1).copied().sum::<L>())
            .sum();
        [
            L::ZERO,
            L::ONE,
            crate::field::from_b(omega()),
            crate::field::from_b(omega() + crate::field::B::ONE),
        ][..self.polys[i].len()]
            .iter()
            .map(|&x| c * Self::eval_poly(&self.polys[i], x) + (L::ONE + x) * (past + c * future))
            .collect()
    }
    pub fn value(&self, p: &[L]) -> L {
        self.polys
            .iter()
            .enumerate()
            .map(|(i, c)| {
                Self::eval_poly(c, p[i])
                    * p.iter()
                        .enumerate()
                        .filter(|&(j, _)| j != i)
                        .map(|(_, &r)| L::ONE + r)
                        .product::<L>()
            })
            .sum()
    }
    pub fn coefficients(&self) -> Vec<L> {
        self.polys.iter().flatten().copied().collect()
    }
}
pub fn g_setup(n: usize, gamma: usize, tau: usize, coeffs: usize) -> (Setup, Vec<usize>) {
    assert!(coeffs > 0, "G coefficient count must be positive");
    let bits = coeffs.checked_mul(crate::field::D).expect("G coefficient count overflow");
    let mut ell = crate::params::ell_for_bits(n, gamma, tau, 2, bits);
    loop {
        let s = Setup::new(crate::params::Params {
            n_parties: n,
            ell,
            beta: 2,
            gamma,
            tau,
            salt_bytes: 32,
        });
        let mut cells=Vec::new();
        for (owner,cols) in s.layout.owned.iter().enumerate() {
            for &x in cols {for y in 0..s.params.k() {
                if s.layout.mask_index(owner,y,x).is_none() {cells.push(y*s.params.n()+x);}
                if cells.len()==coeffs {return (s,cells);}
            }}
        }

        ell += 1;
    }
}
// G coefficients occupy distinct Data cells; validate before indexing or using a transcript.
fn validate_g_map(setup: &Setup, map: &[usize], count: usize) -> Result<(), String> {
    if map.is_empty() || map.len() != count {
        return Err("G map/value length".into());
    }
    let n = setup.params.n();
    let cells = setup.params.k().checked_mul(n).ok_or("G table size")?;
    let mut seen = std::collections::HashSet::with_capacity(map.len());
    for &cell in map {
        let (y, x) = (cell / n, cell % n);
        if cell >= cells || !seen.insert(cell) || setup.layout.pad.binary_search(&x).is_ok()
            || setup.layout.masks.iter().flatten().any(|m| m.y == y && m.x == x)
        {
            return Err("G map must contain distinct Data cells".into());
        }
    }
    Ok(())
}

pub fn g_witness(setup: &Setup, map: &[usize], coeffs: &[L]) -> Witness {
    validate_g_map(setup, map, coeffs.len()).expect("invalid G witness map");
    let mut table = vec![L::ZERO; setup.params.k() * setup.params.n()];
    for (&x, &v) in map.iter().zip(coeffs) {
        table[x] = v;
    }
    Witness { table }
}
pub fn selector_weights(p: &[L], degree: usize) -> Vec<L> {
    let mut w = Vec::new();
    for i in 0..p.len() {
        let c: L = p
            .iter()
            .enumerate()
            .filter(|&(j, _)| j != i)
            .map(|(_, &r)| L::ONE + r)
            .product();
        let mut x = c;
        for _ in 0..=degree {
            w.push(x);
            x *= p[i];
        }
    }
    w
}
/// One G opening. It uses all existing whole random padding columns and tail/query checks.
pub fn open_g(
    setup: &Setup,
    map: &[usize],
    weights: &[L],
    prepared: Prepared,
    tr: &mut Transcript<'_, H>,
) -> Proof {
    validate_g_map(setup, map, weights.len()).expect("invalid G opening map");
    let p = &setup.params;
    assert_eq!(prepared.role, G_ROLE, "G prepared role");
    assert_eq!(prepared.parties.len(), p.n_parties, "G prepared party count");
    assert!(prepared.parties.iter().enumerate().all(|(i, q)|
        q.id == i && q.row.len() == p.n() && q.codewords.len() == 1
        && q.subtrees.len() == 1 && q.salts.len() == 1), "G prepared shape");
    let hasher = Hasher::<H>::scoped(G_ROLE);
    let mut parties = prepared.parties;
    let mut roots = vec![prepared.root];
    let zero = [0; 32];
    let mut c = tr.round(&prepared.root, b"v04 G functional");
    let omega: Vec<L> = (0..setup.n_omega()).map(|_| c.field()).collect();
    let mw = setup.mask_weight(&omega);
    let h_omega: L = crate::transport::scalars(crate::parallel::parties(&mut parties, |_,q| q.h_omega(setup,&mw))).into_iter().sum();
    let eps = tr.round(&zero, bytemuck::cast_slice(&[h_omega])).field();
    assert_ne!(eps, L::ZERO);
    assert!(!omega.contains(&L::ZERO));
    crate::parallel::parties(&mut parties, |_,q| {
        q.weight = vec![L::ZERO; p.n()];
        for (&cell, &w) in map.iter().zip(weights) {
            let (y,x)=(cell/p.n(),cell%p.n());
            q.weight[x] += setup.lagrange[q.id][y] * w;
        }
        for &(x, w) in &mw {
            q.weight[x] += setup.lagrange[q.id][0] * eps * w;
        }
    });
    let mut coeffs = Vec::new();
    for j in 0..p.folds() {
        let (mut a, mut b) = (L::ZERO, L::ZERO);
        let partials=crate::parallel::parties(&mut parties, |_,q| q.round_poly());
        for [x,y] in crate::transport::arrays(partials.into_iter().map(|(x,y)|[x,y]).collect()) {
            a += x;
            b += y;
        }
        coeffs.push((a, b));
        let r = tr
            .round(
                if j == 0 { &zero } else { &roots[j] },
                bytemuck::cast_slice(&[a, b]),
            )
            .field();
        assert_ne!(r, L::ONE);
        crate::parallel::parties(&mut parties, |_,q| q.fold(setup,&Hasher::<H>::scoped(G_ROLE),j,r));
        if j + 1 < p.folds() {
            roots.push(
                Tree::build(
                    &hasher.at_layer((j + 1) as u64),
                    crate::transport::hashes(parties.iter().map(|q| q.subtrees[j + 1].root()).collect()),
                )
                .root(),
            );
        }
    }
    let mut tail_salts = Vec::new();
    let mut leaves = Vec::new();
    for q in &mut parties {
        let mut salt = [0; 32];
        q.rng.fill_bytes(&mut salt);
        leaves.push(hasher.at_layer(TAG_TAIL).leaf(
            TAG_TAIL,
            q.id as u64,
            bytemuck::cast_slice(&q.row),
            &salt,
        ));
        tail_salts.push(salt);
    }
    let tail_root = Tree::build(&hasher.at_layer(TAG_TAIL), crate::transport::hashes(leaves)).root();
    let queries = protocol::sample_queries(setup, tr, &tail_root);
    let tops: Vec<_> = (0..p.folds())
        .map(|j| {
            Tree::build(
                &hasher.at_layer(j as u64),
                parties.iter().map(|q| q.subtrees[j].root()).collect(),
            )
        })
        .collect();
    let openings = queries
        .iter()
        .map(|&(i, q)| {
            (0..p.folds())
                .map(|j| {
                    let x = q >> j;
                    let party = &parties[i];
                    let mut path = party.subtrees[j].path(x);
                    path.extend(tops[j].path(i));
                    protocol::Opening {
                        values: [party.codewords[j][2 * x], party.codewords[j][2 * x + 1]],
                        salt: party.salts[j][x],
                        path,
                    }
                })
                .collect()
        })
        .collect();
    let openings=crate::transport::openings(openings,&queries,p.n_parties);
    let tails=crate::transport::values(parties.iter().map(|q|q.row.clone()).collect(),true);
    let tail_salts=crate::transport::hashes(tail_salts);
    Proof {
        roots,
        tail_root,
        xi: L::ZERO,
        t: vec![],
        h_omega,
        coeffs,
        tails,
        tail_salts,
        openings,
    }
}
pub fn verify_g(
    setup: &Setup,
    map: &[usize],
    weights: &[L],
    value: L,
    proof: &Proof,
    tr: &mut Transcript<'_, H>,
) -> Result<(), String> {
    validate_g_map(setup, map, weights.len())?;
    let p = &setup.params;
    let hasher = Hasher::<H>::scoped(G_ROLE);
    let zero = [0; 32];
    if proof.roots.len() != p.folds()
        || proof.coeffs.len() != p.folds()
        || !proof.t.is_empty()
        || proof.xi != L::ZERO
    {
        return Err("G shape".into());
    }
    let mut c = tr.round(&proof.roots[0], b"v04 G functional");
    let omega: Vec<_> = (0..setup.n_omega()).map(|_| c.field()).collect();
    let eps = tr
        .round(&zero, bytemuck::cast_slice(&[proof.h_omega]))
        .field();
    if eps == L::ZERO || omega.contains(&L::ZERO) {
        return Err("G excluded".into());
    }
    let mut s = value + eps * proof.h_omega;
    let mut r = Vec::new();
    for j in 0..p.folds() {
        let (a, b) = proof.coeffs[j];
        let x = tr
            .round(
                if j == 0 { &zero } else { &proof.roots[j] },
                bytemuck::cast_slice(&[a, b]),
            )
            .field();
        if x == L::ONE {
            return Err("G excluded fold".into());
        }
        s = a + (s + b) * x + b * x * x;
        r.push(x);
    }
    let mut wf = vec![vec![L::ZERO; 1 << p.tau]; p.k()];
    for (&cell, &w) in map.iter().zip(weights) {
        let (y,x)=(cell/p.n(),cell%p.n());
        wf[y][x >> p.folds()] += chi(x & ((1 << p.folds()) - 1), &r) * w;
    }
    for (x, w) in setup.mask_weight(&omega) {
        wf[0][x >> p.folds()] += eps * chi(x & ((1 << p.folds()) - 1), &r) * w;
    }
    protocol::verify_backend(setup, proof, tr, &hasher, &r, &wf, s)?;
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    use rand::{SeedableRng, rngs::StdRng};
    // Missing map/arity checks would silently prove a prefix or overwrite a coefficient.
    #[test]
    fn g_witness_rejects_invalid_maps_and_arity() {
        let (s,map)=g_setup(8,16,3,6);
        let mask=s.layout.masks.iter().flatten().next().unwrap();
        let mut bad_maps=vec![map[..5].to_vec()];
        for cell in [map[1],s.params.k()*s.params.n(),s.layout.pad[0],mask.y*s.params.n()+mask.x] {
            let mut bad=map.clone();bad[0]=cell;bad_maps.push(bad);
        }
        for bad in bad_maps {
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                g_witness(&s,&bad,&[L::ONE;6]))).is_err());
        }
    }

    // A verifier boundary must reject before consuming any Fiat-Shamir challenge.
    #[test]
    fn g_verifier_rejects_invalid_maps_before_transcript() {
        let mut rng=StdRng::seed_from_u64(0x4756414c);
        let(s,map)=g_setup(8,16,3,6);
        let wit=g_witness(&s,&map,&[L::ONE;6]);
        let prepared=protocol::prepare_random::<H>(&s,&wit,&mut rng,G_ROLE);
        let h=Hasher::<H>::default();let mut tr=Transcript::new_global(&h,b"G-validation");
        let proof=open_g(&s,&map,&[L::ONE;6],prepared,&mut tr);
        let mask=s.layout.masks.iter().flatten().next().unwrap();
        let mut cases=vec![(map.clone(),vec![L::ONE;5])];
        for cell in [map[1],s.params.k()*s.params.n(),s.layout.pad[0],mask.y*s.params.n()+mask.x] {
            let mut bad=map.clone();bad[0]=cell;cases.push((bad,vec![L::ONE;6]));
        }
        cases.push((vec![],vec![]));
        for (bad,w) in cases {
            let mut tv=Transcript::new_global(&h,b"G-validation");let before=tv.state();
            assert!(verify_g(&s,&bad,&w,L::ZERO,&proof,&mut tv).is_err());
            assert_eq!(before,tv.state(),"invalid G arguments changed the transcript");
        }
    }

    #[test]
    #[should_panic(expected="G coefficient count")]
    fn g_setup_rejects_zero_count() { g_setup(8,16,3,0); }

    #[test]
    #[should_panic(expected="G coefficient count")]
    fn g_setup_rejects_count_overflow() { g_setup(8,16,3,usize::MAX); }

    // BIT_ROLE codewords cannot be consumed as G_ROLE committed server state.
    #[test]
    fn g_prover_rejects_wrong_prepared_role_before_transcript() {
        let mut rng=StdRng::seed_from_u64(0x47524f4c);
        let(s,map)=g_setup(8,16,3,6);let wit=g_witness(&s,&map,&[L::ONE;6]);
        let prepared=protocol::prepare_random::<H>(&s,&wit,&mut rng,BIT_ROLE);
        let h=Hasher::<H>::default();let mut tr=Transcript::new_global(&h,b"G-role");
        let before=tr.state();
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            open_g(&s,&map,&[L::ONE;6],prepared,&mut tr))).is_err());
        assert_eq!(before,tr.state());
    }

    #[test]
    fn g_prover_rejects_invalid_map_and_prepared_shape_before_transcript() {
        let mut rng=StdRng::seed_from_u64(0x47534850);
        let(s,map)=g_setup(8,16,3,6);let wit=g_witness(&s,&map,&[L::ONE;6]);
        let h=Hasher::<H>::default();
        for kind in 0..4 {
            let mut prepared=protocol::prepare_random::<H>(&s,&wit,&mut rng,G_ROLE);
            let mut bad=map.clone();
            match kind {
                0 => { bad.pop(); },
                1 => { prepared.parties.pop(); },
                2 => { prepared.parties[0].row.pop(); },
                _ => { bad[0]=s.layout.pad[0]; },
            }
            let mut tr=Transcript::new_global(&h,b"G-prover-shape");let before=tr.state();
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                open_g(&s,&bad,&[L::ONE;6],prepared,&mut tr))).is_err());
            assert_eq!(before,tr.state());
        }
    }

    #[test]
    fn global_capacity_multirow_g_opens_the_actual_linear_functional() {
        let mut rng=StdRng::seed_from_u64(0x47524f57);
        let (s,map)=g_setup(8,871,4,155);
        assert_eq!(s.params.ell,12);
        assert!(map.iter().any(|&cell|cell>=s.params.n()));
        let coeffs:Vec<L>=(0..155).map(|_|L::random(&mut rng)).collect();
        let weights:Vec<L>=(0..155).map(|_|L::random(&mut rng)).collect();
        let value:L=coeffs.iter().zip(&weights).map(|(&a,&b)|a*b).sum();
        let wit=g_witness(&s,&map,&coeffs);
        assert_eq!(map.iter().zip(&weights).map(|(&cell,&w)|wit.table[cell]*w).sum::<L>(),value);
        let prepared=protocol::prepare_random::<H>(&s,&wit,&mut rng,G_ROLE);
        let h=Hasher::<H>::default();let mut tr=Transcript::new_global(&h,b"multirow-G");
        let proof=open_g(&s,&map,&weights,prepared,&mut tr);
        let mut tv=Transcript::new_global(&h,b"multirow-G");
        verify_g(&s,&map,&weights,value,&proof,&mut tv).unwrap();
        let mut tv=Transcript::new_global(&h,b"multirow-G");
        assert!(verify_g(&s,&map,&weights,value+L::ONE,&proof,&mut tv).is_err());
    }

    #[test]
    fn selector_rounds_and_weighted_fold() {
        let mut rng = StdRng::seed_from_u64(77);
        let g = Selector::random(3, 3, &mut rng);
        let mut r = Vec::new();
        let mut claim = g.sum();
        for _ in 0..3 {
            let q = g.round(&r);
            assert_eq!(q[0] + q[1], claim);
            let x = L::random(&mut rng);
            claim = crate::spartan::interp(&q, x);
            r.push(x);
        }
        assert_eq!(claim, g.value(&r));
        let (s, map) = g_setup(8, 16, 3, 12);
        let w = selector_weights(&r, 3);
        let wit = g_witness(&s, &map, &g.coefficients());
        let prepared = protocol::prepare_random::<H>(&s, &wit, &mut rng, G_ROLE);
        let h = Hasher::<H>::default();
        let mut t = Transcript::new_global(&h, b"g-test");
        let proof = open_g(&s, &map, &w, prepared, &mut t);
        let mut tv = Transcript::new_global(&h, b"g-test");
        verify_g(&s, &map, &w, g.value(&r), &proof, &mut tv).unwrap();
        assert_eq!(t.state(), tv.state());
        let mut tv = Transcript::new_global(&h, b"g-test");
        assert!(verify_g(&s, &map, &w, g.value(&r) + L::ONE, &proof, &mut tv).is_err());
    }
}
