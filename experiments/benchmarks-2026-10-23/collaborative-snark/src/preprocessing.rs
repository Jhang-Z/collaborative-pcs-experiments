//! Immutable public preprocessing, generated before online commitments.
use crate::{field::{Field,L,eq_expand}, sha_zk::Config, sha_spartan::sparse_pairs};
use binius_field::arithmetic_traits::InvertOrZero;
use std::{mem::size_of,ops::Deref};

pub(crate) struct PublicPreprocessing {
    pub cfg: Config,
    pub indices: Vec<usize>,
    pub sc2_schedule: Vec<Vec<[Option<usize>;2]>>,
    pub lag_eta0: Vec<L>,
    pub conversion_weights: Vec<Vec<L>>,
    public_positions: Vec<Vec<usize>>,
}
impl Deref for PublicPreprocessing {
    type Target=Config;
    fn deref(&self)->&Config {&self.cfg}
}
fn normalize_rows(rows:&[Vec<L>],ordinary:&[L])->Vec<Vec<L>> {
    rows.iter().zip(ordinary).map(|(row,&lag)| {
        let inverse=lag.invert_or_zero();
        row.iter().map(|&v|v*inverse).collect()
    }).collect()
}
pub(crate) fn context_cache_payload_bytes(cfg:&Config)->usize {
    cfg.ctx.kp*cfg.ctx.k*size_of::<L>()
    +cfg.pcs.mask_cache_payload_bytes()+cfg.g.mask_cache_payload_bytes()
}
pub(crate) fn fixed_interpolation_payload_bytes()->usize {size_of::<[[L;4];5]>()}
impl PublicPreprocessing {
    pub fn new(cfg:Config,digests:Vec<[u8;32]>)->Self {
        assert_eq!(digests.len(),cfg.batch());
        let indices:Vec<usize>=(0..cfg.groups).flat_map(|g|
            (0..cfg.circuit.private_len).map(|p|cfg.map[p+cfg.circuit.base.n0()*g]).collect::<Vec<_>>()
        ).collect();
        let mut current=indices.clone();let mut sc2_schedule=Vec::new();
        for _ in 0..cfg.sc2_len() {
            let (parents,pairs)=sparse_pairs(&current);
            sc2_schedule.push(pairs);current=parents;
        }
        let lag_eta0=cfg.ctx.lag_eta0();
        let conversion_weights=normalize_rows(&cfg.ctx.lag_n,&lag_eta0);
        let public_positions=digests.iter().map(|d|cfg.circuit.public(d).iter().enumerate()
            .filter_map(|(i,&bit)|bit.then_some(i)).collect()).collect();
        Self{cfg,indices,sc2_schedule,lag_eta0,conversion_weights,public_positions}
    }
    // Challenge-dependent coefficients remain online; only addresses/public bits are cached.
    pub fn weight_values(&self,rcol:&[L],ry:&[L],rho:[L;3])->(Vec<L>,L) {
        let base=&self.circuit.base;
        let w0=base.weight(&eq_expand(&rcol[..base.log_m0]),rho);
        let eg=eq_expand(&rcol[base.log_m0..]);let ey=eq_expand(ry);
        let mut w=Vec::with_capacity(self.indices.len());
        for &group in &eg {w.extend(w0[..self.circuit.private_len].iter().map(|&v|v*group));}
        let mut public=L::ZERO;
        for y in 0..self.ctx.k {for g in 0..self.groups {
            let sum:L=self.public_positions[g+self.groups*y].iter()
                .map(|&i|w0[self.circuit.private_len+i]).sum();
            public+=ey[y]*eg[g]*sum;
        }}
        (w,public)
    }
    /// Additional payload only, excluding Vec headers/capacity and existing NTT/layouts.
    pub fn cache_payload_bytes(&self)->usize {
        self.indices.len()*size_of::<usize>()
        +self.sc2_schedule.iter().map(|v|v.len()*size_of::<[Option<usize>;2]>()).sum::<usize>()
        +self.public_positions.iter().map(|v|v.len()*size_of::<usize>()).sum::<usize>()
        +(self.lag_eta0.len()+self.conversion_weights.iter().map(Vec::len).sum::<usize>())*size_of::<L>()
        +context_cache_payload_bytes(&self.cfg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{sha_zk::Config, field::{Field,L,Random,chi},sha_spartan::sparse_fold};
    use rand::{SeedableRng,rngs::StdRng};
    #[test]
    fn cached_sparse_schedule_matches_direct_mle_with_high_tail_rounds() {
        let cfg=Config::synthetic(8,2,16,3,64);
        let prepared=PublicPreprocessing::new(cfg,vec![[0;32];4]);
        let mut rng=StdRng::seed_from_u64(20261030);
        let point:Vec<L>=(0..prepared.sc2_len()).map(|_|L::random(&mut rng)).collect();
        let original:Vec<L>=prepared.indices.iter().map(|_|L::random(&mut rng)).collect();
        let expected:L=prepared.indices.iter().zip(&original).map(|(&i,&x)|chi(i,&point)*x).sum();
        assert_eq!(prepared.sc2_schedule.len(),point.len());
        let mut folded=original;
        for (pairs,&r) in prepared.sc2_schedule.iter().zip(&point) {folded=sparse_fold(&folded,pairs,r);}
        assert_eq!(folded,vec![expected]);
    }
    #[test]
    fn prepared_public_weights_match_legacy_ordered_digest_relation() {
        let cfg=Config::synthetic(8,2,16,3,64);
        let digests=vec![[0;32],[255;32],[1;32],[128;32]];
        let prepared=PublicPreprocessing::new(cfg,digests.clone());
        let mut rng=StdRng::seed_from_u64(20261031);
        for _ in 0..4 {
            let rcol:Vec<L>=(0..prepared.sc1_len()-prepared.pcs.log_k()).map(|_|L::random(&mut rng)).collect();
            let ry:Vec<L>=(0..prepared.pcs.log_k()).map(|_|L::random(&mut rng)).collect();
            let rho=std::array::from_fn(|_|L::random(&mut rng));
            let (indices,w,public)=prepared.cfg.weights(&rcol,&ry,rho,&digests);
            assert_eq!(indices,prepared.indices);
            assert_eq!(prepared.weight_values(&rcol,&ry,rho),(w,public));
        }
    }
    #[test]
    fn normalization_preserves_invert_or_zero_semantics() {
        let row=vec![L::ONE,L::ZERO];
        assert_eq!(normalize_rows(&[row.clone()],&[L::ZERO]),vec![vec![L::ZERO;2]]);
        assert_eq!(normalize_rows(&[row.clone()],&[L::ONE]),vec![row]);
    }
    #[test]
    fn normalized_conversion_reconstructs_packed_products_for_every_party_count() {
        use crate::field::{B,from_b};
        let mut rng=StdRng::seed_from_u64(20261101);
        for n in [8,16,32,64,128,256] {
            let cfg=Config::synthetic(n,1,16,3,64);
            let prepared=PublicPreprocessing::new(cfg,vec![[0;32];n/4]);
            let left:Vec<bool>=(0..n/4).map(|i|i%3==0).collect();
            let right:Vec<bool>=(0..n/4).map(|i|i%2==0).collect();
            let mut a=vec![B::ZERO;n];let mut b=vec![B::ZERO;n];
            prepared.ctx.share_bits(|y|left[y],&mut rng,&mut a);
            prepared.ctx.share_bits(|y|right[y],&mut rng,&mut b);
            for y in 0..n/4 {
                let value:L=(0..n).map(|i|prepared.lag_eta0[i]*prepared.conversion_weights[i][y]*from_b(a[i]*b[i])).sum();
                assert_eq!(value,if left[y]&&right[y] {L::ONE} else {L::ZERO},"N={n},slot={y}");
            }
        }
    }

}
