//! Online kernel benchmark with synthetic state, following the authors' Liu benchmark boundary.
use crate::{
    field::{B, Field, L, Random}, prepare::{self, Shape, Shares},
    sha_zk::Config, spartan::PartyShares, zk::Selector,
};
use anyhow::{Result, ensure};
use rand::{Rng, rngs::StdRng};
use std::{fs, path::Path, time::Instant};

pub(crate) fn state(cfg: &Config, rng: &mut StdRng) -> Shares {
        // Keep the real private-prefix/public-padding pattern in the PIOP table.
        let mut z=vec![B::ZERO;cfg.circuit.base.n0()*cfg.groups];
        for group in z.chunks_exact_mut(cfg.circuit.base.n0()) {
            for value in &mut group[..cfg.circuit.private_len] {*value=B::random(&mut *rng);}
        }
        Shares {
            piop:PartyShares { z, rows:std::array::from_fn(|_|
                (0..cfg.circuit.base.m0()*cfg.groups).map(|_|B::random(&mut *rng)).collect()) },
            masks:[Selector::random(cfg.sc1_len(),3,rng),Selector::random(cfg.sc2_len(),2,rng)],
            nonce:L::random(&mut *rng),
            packed:std::array::from_fn(|_|L::random(&mut *rng)),
            ordinary:std::array::from_fn(|_|(0..cfg.ctx.k).map(|_|L::random(&mut *rng)).collect()),
            main:(0..cfg.pcs.params.n()).map(|_|L::random(&mut *rng)).collect(),
            g:(0..cfg.g.params.n()).map(|_|L::random(&mut *rng)).collect(),
        }
}

#[cfg(test)]
pub(crate) fn states(cfg: &Config, rng: &mut StdRng) -> Vec<Shares> {
    (0..cfg.ctx.n).map(|_|state(cfg,rng)).collect()
}

pub fn run(shape: Shape, out: &Path, trace: &Path) -> Result<()> {
    ensure!(!out.exists(),"use a fresh benchmark directory");
    let start=Instant::now();
    let cfg=shape.config()?;
    let mut rng=prepare::entropy()?;
    // Random public bits retain representative public-vector work as well.
    let mut statement=vec![0;shape.messages*32]; rng.fill_bytes(&mut statement);
    fs::create_dir(out)?;
    fs::write(out.join("shape.json"),serde_json::to_vec_pretty(&shape)?)?;
    fs::write(out.join("statement.bin"),statement)?;
    crate::coordinator::simulate_benchmark(out,trace,cfg,start)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    #[test]
    fn synthetic_state_preserves_array_dimensions_and_zero_padding() {
        let cfg=Config::synthetic(8,2,16,3,64);
        let states=states(&cfg,&mut StdRng::seed_from_u64(20261031));
        assert_eq!(states.len(),cfg.ctx.n);
        for state in states {
            assert_eq!(state.piop.z.len(),cfg.circuit.base.n0()*cfg.groups);
            for group in state.piop.z.chunks_exact(cfg.circuit.base.n0()) {
                assert!(group[cfg.circuit.private_len..].iter().all(|v|*v==B::ZERO));
            }
            for row in &state.piop.rows {assert_eq!(row.len(),cfg.circuit.base.m0()*cfg.groups);}
            assert_eq!(state.main.len(),cfg.pcs.params.n());
            assert_eq!(state.g.len(),cfg.g.params.n());
            assert_eq!(state.masks[0].polys.len(),cfg.sc1_len());
            assert_eq!(state.masks[1].polys.len(),cfg.sc2_len());
            assert!(state.masks[0].polys.iter().all(|p|p.len()==4));
            assert!(state.masks[1].polys.iter().all(|p|p.len()==3));
            assert!(state.ordinary.iter().all(|v|v.len()==cfg.ctx.k));
        }
    }
}
