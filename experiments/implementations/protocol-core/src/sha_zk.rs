//! v0.5 composition in the ideal-functionality model; optional concurrent party execution.
use crate::{
    field::{B, D, Field, L, Random, eq_expand, from_b, from_words},
    fs::Transcript,
    merkle::{Hash, Hasher},
    protocol::{self, Proof as PcsProof},
    setup::{Instance, Setup, Witness},
    spartan::{PTimes, PartyShares, eq_eval, fold_b, fold_l, interp, round_b, round_l},
};
use binius_field::arithmetic_traits::InvertOrZero;
use binius_hash::Blake3HashSuite as H;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};

const ZERO: Hash = [0; 32];

#[cfg(test)]
mod hash_configuration_tests {
    use super::*;
    use binius_hash::Blake3HashSuite;

    #[test]
    fn internal_merkle_and_fs_suite_is_blake3() {
        let actual = Hasher::<H>::scoped(1);
        let expected = Hasher::<Blake3HashSuite>::scoped(1);
        assert_eq!(actual.hash(&[b"suite-regression"]), expected.hash(&[b"suite-regression"]));
        assert_eq!(actual.leaf(1, 0, b"payload", &[0; 32]), expected.leaf(1, 0, b"payload", &[0; 32]));
        assert_eq!(actual.node(&[1; 32], &[2; 32]), expected.node(&[1; 32], &[2; 32]));
    }
}

use crate::{
    sha_spartan::{Config as Inner, sparse_fold, sparse_pairs, sparse_round},
    zk::{self, Selector},
};
use std::{io::Read, ops::Deref};
pub struct Config {
    pub inner: Inner,
    pub g: Setup,
    pub gmap: Vec<usize>,
}
impl Deref for Config {
    type Target = Inner;
    fn deref(&self) -> &Inner {
        &self.inner
    }
}
impl Config {
    pub fn new(n: usize, groups: usize, gamma: usize, tau: usize) -> Self {
        let inner = Inner::new_zk(n, groups, gamma, tau);
        let (g, gmap) = zk::g_setup(n, gamma, tau, 4 * inner.sc1_len() + 3 * inner.sc2_len());
        Self { inner, g, gmap }
    }
    pub fn new_keccak(n:usize,groups:usize,gamma:usize,tau:usize)->Self {
        let inner=Inner::from_circuit(n,groups,gamma,tau,crate::sha_circuit::ShaCircuit::new_keccak_zk());
        let(g,gmap)=zk::g_setup(n,gamma,tau,4*inner.sc1_len()+3*inner.sc2_len());Self{inner,g,gmap}
    }
    pub fn synthetic(n:usize,groups:usize,gamma:usize,tau:usize,gates:usize)->Self {
        let inner=Inner::from_circuit(n,groups,gamma,tau,crate::sha_circuit::ShaCircuit::synthetic_zk(gates));
        let (g,gmap)=zk::g_setup(n,gamma,tau,4*inner.sc1_len()+3*inner.sc2_len());Self{inner,g,gmap}
    }
    pub(crate) fn statement(&self, d: &[[u8; 32]]) -> Vec<u8> {
        let mut v = b"sha256-v04-zk-blake3".to_vec();
        v.extend(self.inner.statement(d));
        v.extend_from_slice(&(self.g.params.ell as u64).to_le_bytes());
        v
    }
}
#[derive(Clone)]
pub struct Proof {
    pub nonce: Hash,
    pub top: Hash,
    pub h1: L,
    pub h2: L,
    pub y1: L,
    pub y2: L,
    pub conversions: Vec<Vec<L>>,
    pub g: PcsProof,
    pub sc1: Vec<[L; 4]>,
    pub endpoints: [L; 3],
    pub sc2: Vec<[L; 3]>,
    pub value: L,
    pub pcs: PcsProof,
}
#[derive(Default)]
pub struct Times {
    pub mask: Duration,
    pub g_prepare: Duration,
    pub g_share: Duration,
    pub g_random: Duration,
    pub pcs_pack: Duration,
    pub g_open: Duration,
    pub nonce: Duration,
    pub witness: Duration,
    pub piop_share: Duration,
    pub pcs_prepare: Duration,
    pub pcs_random: Duration,
    pub pcs_share: Duration,
    pub piop: Duration,
    pub public_input_proof: Duration,
    pub public_matrix_proof: Duration,
    pub conversion_preprocess: Duration,
    pub conversion_online: Duration,
    pub pcs_open: Duration,
    pub verify: Duration,
    pub total: Duration,
    pub parties: Vec<PTimes>,
}
pub struct Run {
    pub proof: Proof,
    pub digests: Vec<[u8; 32]>,
    pub times: Times,
}
fn bytes(v: &[L]) -> &[u8] {
    bytemuck::cast_slice(v)
}

pub fn prove(cfg: &Config, seed: u64) -> Run {
    let mut entropy = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .expect("OS randomness")
        .read_exact(&mut entropy)
        .unwrap();
    prove_with_rng(cfg, seed, StdRng::from_seed(entropy))
}
fn prove_with_rng(cfg: &Config, seed: u64, rng: StdRng) -> Run { prove_core(cfg,seed,rng,None).0 }
pub(crate) fn prove_core(cfg:&Config,seed:u64,rng:StdRng,index:Option<&crate::indexed::Index>)->(Run,Option<crate::indexed::MatrixProof>) {
    prove_core_input(cfg,seed,rng,index,None,true,None)
}
/// External SHA messages; final verification is deliberately left to an independent caller.
/// This still includes witness construction and preprocessing, so its duration is not online time.
pub(crate) fn prove_core_messages(cfg:&Config,messages:&[[u8;32]],rng:StdRng,index:&crate::indexed::Index)->(Run,Option<crate::indexed::MatrixProof>) {
    assert_eq!(messages.len(),cfg.batch(),"SHA message count");
    prove_core_input(cfg,0,rng,Some(index),Some(messages),false,None)
}
/// The structured wrapper supplies its fixed-relation statement; no matrix index is used.
pub(crate) fn prove_core_structured_messages(cfg:&Config,messages:&[[u8;32]],rng:StdRng,statement:&[u8])->Run {
    assert_eq!(messages.len(),cfg.batch(),"SHA message count");
    prove_core_input(cfg,0,rng,None,Some(messages),false,Some(statement)).0
}
fn prove_core_input(cfg:&Config,seed:u64,mut rng:StdRng,index:Option<&crate::indexed::Index>,messages:Option<&[[u8;32]]>,verify_after:bool,statement_override:Option<&[u8]>)->(Run,Option<crate::indexed::MatrixProof>) {
    assert!(statement_override.is_none() || (index.is_none() && !verify_after));
    let total = Instant::now();
    let mut tm = Times::default();
    let (ctx, base, g) = (&cfg.ctx, &cfg.circuit.base, cfg.groups);
    let (n, k, n0, m0) = (ctx.n, ctx.k, base.n0(), base.m0());
    let mut inputs = StdRng::seed_from_u64(seed);
    let t = Instant::now();
    let copies: Vec<_> = (0..cfg.batch())
        .map(|i| {
            let msg = if let Some(messages)=messages {messages[i]} else {
                let mut msg=[0u8;32];inputs.fill_bytes(&mut msg);msg
            };
            let mut c = cfg.circuit.witness(&msg);
            cfg.circuit.randomize_masks(&mut c.0, &mut c.1, &mut rng);
            if index.is_none() || messages.is_some() {assert_eq!(c.2.as_slice(), Sha256::digest(msg).as_slice(),"standard SHA-256 digest");}
            c
        })
        .collect();
    let digests: Vec<_> = copies.iter().map(|c| c.2).collect();
    tm.witness = t.elapsed();
    let t = Instant::now();
    let sel = [
        Selector::random(cfg.sc1_len(), 3, &mut rng),
        Selector::random(cfg.sc2_len(), 2, &mut rng),
    ];
    let coefficients: Vec<L> = sel.iter().flat_map(Selector::coefficients).collect();
    let mut masks: Vec<[Selector; 2]> = (0..n)
        .map(|_| {
            [
                Selector {
                    polys: vec![vec![L::ZERO; 4]; cfg.sc1_len()],
                },
                Selector {
                    polys: vec![vec![L::ZERO; 3]; cfg.sc2_len()],
                },
            ]
        })
        .collect();
    for a in 0..2 {
        for j in 0..sel[a].polys.len() {
            for u in 0..sel[a].polys[j].len() {
                let sh = ctx.share_sss(sel[a].polys[j][u], &mut rng);
                for i in 0..n {
                    masks[i][a].polys[j][u] = sh[i];
                }
            }
        }
    }
    if crate::transport::enabled(){
        let received=crate::transport::values(masks.iter().map(|m|m.iter().flat_map(Selector::coefficients).collect()).collect(),false);
        for(m,v)in masks.iter_mut().zip(received){let mut at=0;for sel in m {for poly in &mut sel.polys{let len=poly.len();poly.copy_from_slice(&v[at..at+len]);at+=len;}}}
    }
    let gw = zk::g_witness(&cfg.g, &cfg.gmap, &coefficients);
    tm.mask = t.elapsed();
    let t = Instant::now();
    let gprepared = protocol::prepare_random::<H>(&cfg.g, &gw, &mut rng, zk::G_ROLE);
    tm.g_prepare = t.elapsed();
    tm.g_share=gprepared.client_share;tm.g_random=gprepared.preprocessing;
    drop(gw);
    drop(sel);
    drop(coefficients);
    let t = Instant::now();
    let mut parties: Vec<_> = (0..n)
        .map(|_| PartyShares {
            z: vec![B::ZERO; n0 * g],
            rows: std::array::from_fn(|_| vec![B::ZERO; m0 * g]),
        })
        .collect();
    let mut buf = vec![B::ZERO; n];
    for gg in 0..g {
        for p in 0..cfg.circuit.private_len {
            ctx.share_bits(|y| copies[gg + g * y].0[p], &mut rng, &mut buf);
            for i in 0..n {
                parties[i].z[p + n0 * gg] = buf[i];
            }
        }
        for a in 0..3 {
            for j in 0..m0 {
                ctx.share_bits(|y| copies[gg + g * y].1[a][j], &mut rng, &mut buf);
                for i in 0..n {
                    parties[i].rows[a][j + m0 * gg] = buf[i];
                }
            }
        }
    }
    if crate::transport::enabled(){
        let received=crate::transport::values(parties.iter().map(|p|p.z.iter().chain(p.rows.iter().flatten()).copied().collect()).collect(),false);
        for(p,v)in parties.iter_mut().zip(received){let len=p.z.len();p.z.copy_from_slice(&v[..len]);let mut at=len;for row in &mut p.rows{row.copy_from_slice(&v[at..at+m0*g]);at+=m0*g;}}
    }
    tm.piop_share = t.elapsed();
    let t = Instant::now();
    let cols = cfg.pcs.params.n();
    let mut packed = vec![[0u128; 2]; k * cols];
    for y in 0..k {
        for gg in 0..g {
            for p in 0..cfg.circuit.private_len {
                if copies[gg + g * y].0[p] {
                    let a = cfg.map[p + n0 * gg];
                    let (h, x) = (a % D, a / D);
                    packed[y * cols + x][h / 128] |= 1u128 << (h % 128);
                }
            }
        }
    }
    let mut wit = Witness {
        table: packed.into_iter().map(from_words).collect(),
    };
    for m in cfg.pcs.layout.masks.iter().flatten() {
        wit.table[m.y * cols + m.x] = L::random(&mut rng);
    }
    tm.pcs_pack=t.elapsed();
    let prepared = protocol::prepare_random::<H>(&cfg.pcs, &wit, &mut rng, zk::BIT_ROLE);
    tm.pcs_random = prepared.preprocessing;
    tm.pcs_share = prepared.client_share;
    tm.pcs_prepare = t.elapsed();
    let root = prepared.root;
    // From here onward the prover uses only server state/shares, not client plaintext.
    drop(wit);
    drop(copies);
    let hasher = Hasher::<H>::default();
    let statement=statement_override.map_or_else(||index.map_or_else(||cfg.statement(&digests),|i|i.statement(cfg,&digests)),<[u8]>::to_vec);
    crate::transport::broadcast(&statement);
    let mut tr = Transcript::new_global(&hasher, &statement);
    let top = hasher.hash(&[b"v04-top", &root, &gprepared.root]);
    let t = Instant::now();
    let nu = L::random(&mut rng);
    let ns=crate::transport::values(ctx.share_sss(nu,&mut rng).into_iter().map(|x|vec![x]).collect(),false);
    let ns=crate::transport::scalars(ns.into_iter().map(|x|x[0]).collect());
    let lag = ctx.lag_eta0();
    let recovered: L = ns.iter().zip(&lag).map(|(&a, &b)| a * b).sum();
    assert_eq!(nu, recovered);
    let nonce: Hash = bytemuck::cast(nu);
    tm.nonce = t.elapsed();
    tr.absorb(b"initial roots", &[root, gprepared.root].concat());
    let mut initial = tr.round(&top, &nonce);
    let tau: Vec<L> = (0..cfg.sc1_len()).map(|_| initial.field()).collect();
    let nv_col = base.log_m0 + g.trailing_zeros() as usize;
    let (eq_col, eq_y) = (eq_expand(&tau[..nv_col]), eq_expand(&tau[nv_col..]));
    let mu: Vec<L> = (0..n)
        .map(|i| (0..k).map(|y| eq_y[y] * ctx.lag_n[i][y]).sum())
        .collect();
    let mut pt = vec![PTimes::default(); n];
    let piop_start = Instant::now();
    let mut st: Vec<(Vec<L>, [Vec<L>; 3])> = (0..n)
        .map(|_| (vec![], std::array::from_fn(|_| vec![])))
        .collect();
    let mut sc1 = Vec::new();
    let mut rcol = Vec::new();
    let lag = ctx.lag_eta0();
    let h1: L = crate::transport::scalars((0..n).map(|i| lag[i] * masks[i][0].sum()).collect()).into_iter().sum();
    let lambda1 = tr.round(&ZERO, bytes(&[h1])).field();
    assert_ne!(lambda1, L::ZERO);
    let mut claim = lambda1 * h1;
    for round in 0..nv_col {
        let mut agg = [L::ZERO; 4];
        let partials=crate::parallel::parties(&mut st, |i,state| {
            let t=Instant::now();
            let v=if round==0 {let [a,b,c]=&parties[i].rows;round_b(&eq_col,a,b,c)}
                else {let(e,[a,b,c])=state;round_l(e,a,b,c)};
            let q=masks[i][0].round(&rcol);
            (std::array::from_fn::<_,4,_>(|u|mu[i]*v[u]+lambda1*lag[i]*q[u]),t.elapsed())
        });
        for(i,(_,elapsed))in partials.iter().enumerate(){pt[i].sc1_col+=*elapsed;}
        for v in crate::transport::arrays(partials.into_iter().map(|x|x.0).collect()){for u in 0..4{agg[u]+=v[u];}}
        assert_eq!(agg[0] + agg[1], claim, "SC1 column");
        let r = tr.round(&ZERO, bytes(&agg)).field();
        assert_ne!(r, L::ONE, "SC1 excluded challenge");
        claim = interp(&agg, r);
        sc1.push(agg);
        rcol.push(r);
        let durations=crate::parallel::parties(&mut st, |i,state| {
            let t=Instant::now();
            *state=if round==0 {let[a,b,c]=&parties[i].rows;(fold_l(&eq_col,r),[fold_b(a,r),fold_b(b,r),fold_b(c,r)])}
                else {let(e,[a,b,c])=&*state;(fold_l(e,r),[fold_l(a,r),fold_l(b,r),fold_l(c,r)])};
            t.elapsed()
        });
        for(i,elapsed)in durations.into_iter().enumerate(){pt[i].sc1_col+=elapsed;}
    }
    let ecr = st[0].0[0];
    let lag = ctx.lag_eta0();
    let mut sss: Vec<[Vec<L>; 3]> = (0..n)
        .map(|_| std::array::from_fn(|_| vec![L::ZERO; k]))
        .collect();
    let mut conversions = Vec::new();
    // Only A and B need degree-reduced ordinary shares. Each double sharing is fresh.
    for a in 0..2 {
        let t = Instant::now();
        let r: Vec<L> = (0..k).map(|_| L::random(&mut rng)).collect();
        let packed:Vec<L>=crate::transport::values(ctx.share_packed(&r,&mut rng).into_iter().map(|x|vec![x]).collect(),false).into_iter().map(|v|v[0]).collect();
        let ordinary: Vec<_> = r.iter().map(|&v| crate::transport::values(ctx.share_sss(v, &mut rng).into_iter().map(|x|vec![x]).collect(),false).into_iter().map(|x|x[0]).collect::<Vec<_>>()).collect();
        tm.conversion_preprocess += t.elapsed();
        let t = Instant::now();
        let masked=crate::transport::scalars((0..n).map(|i| st[i].1[a][0]+packed[i]).collect());
        conversions.push(masked.clone());
        let delta = ctx.open_packed(&masked);
        crate::transport::broadcast(bytes(&delta));
        for i in 0..n {
            for y in 0..k {
                sss[i][a][y] = delta[y] + ordinary[y][i];
            }
        }
        tm.conversion_online += t.elapsed();
    }
    let t = Instant::now();
    for i in 0..n {
        for y in 0..k {
            sss[i][2][y] = ctx.lag_n[i][y] * lag[i].invert_or_zero() * st[i].1[2][0];
        }
    }
    tm.conversion_online += t.elapsed();
    tr.absorb(b"conversions", bytes(&conversions.concat()));
    let mut es: Vec<L> = eq_y.iter().map(|&v| v * ecr).collect();
    let mut ry = Vec::new();
    for _ in 0..cfg.pcs.log_k() {
        let mut agg = [L::ZERO; 4];
        let prefix:Vec<_>=rcol.iter().chain(&ry).copied().collect();
        let partials=crate::parallel::parties(&mut sss, |i,state| {let t=Instant::now();let[a,b,c]=state;let v=round_l(&es,a,b,c);let q=masks[i][0].round(&prefix);(std::array::from_fn::<_,4,_>(|u|lag[i]*(v[u]+lambda1*q[u])),t.elapsed())});
        for(i,(_,elapsed))in partials.iter().enumerate(){pt[i].sc1_slot+=*elapsed;}
        for v in crate::transport::arrays(partials.into_iter().map(|x|x.0).collect()){for u in 0..4{agg[u]+=v[u];}}
        assert_eq!(agg[0] + agg[1], claim, "SC1 slot");
        let r = tr.round(&ZERO, bytes(&agg)).field();
        assert_ne!(r, L::ONE, "SC1 excluded challenge");
        claim = interp(&agg, r);
        sc1.push(agg);
        ry.push(r);
        es = fold_l(&es, r);
        let durations=crate::parallel::parties(&mut sss, |_,state| {let t=Instant::now();for v in state{*v=fold_l(v,r);}t.elapsed()});
        for(i,elapsed)in durations.into_iter().enumerate(){pt[i].sc1_slot+=elapsed;}
    }
    let endpoints: [L; 3] = std::array::from_fn(|a| crate::transport::scalars((0..n).map(|i| lag[i] * sss[i][a][0]).collect()).into_iter().sum());
    let rx: Vec<_> = rcol.iter().chain(&ry).copied().collect();
    let y1: L = crate::transport::scalars((0..n).map(|i| lag[i] * masks[i][0].value(&rx)).collect()).into_iter().sum();
    assert_eq!(
        claim,
        eq_eval(&tau, &rx) * (endpoints[0] * endpoints[1] + endpoints[2]) + lambda1 * y1
    );
    let mut ep = endpoints.to_vec();
    ep.push(y1);
    let mut c = tr.round(&ZERO, bytes(&ep));
    let rho = std::array::from_fn(|_| c.field());
    let (mut indices, mut weights, public) = cfg.weights(&rcol, &ry, rho, &digests);
    let public_started=Instant::now();
    let public_proof=index.map(|i| {
        let input=crate::indexed::public_vector(cfg.groups,cfg.ctx.k,&ry,&digests,cfg.circuit.keccak);
        crate::sparse_matrix::contract_prove(&i.public,&rcol,rho,&input,public,&mut tr)
    });
    tm.public_input_proof=public_started.elapsed();
    let mut claim2: L = rho.iter().zip(endpoints).map(|(&a, b)| a * b).sum::<L>() + public;
    let ey = eq_expand(&ry);
    let mu2: Vec<L> = (0..n)
        .map(|i| (0..k).map(|y| ey[y] * ctx.lag_n[i][y]).sum())
        .collect();
    let prepared_z=crate::parallel::parties(&mut parties, |_,p| {
        let t=Instant::now();let mut z=Vec::with_capacity(weights.len());
        for gg in 0..g {for j in 0..cfg.circuit.private_len {z.push(from_b(p.z[j+n0*gg]));}}
        (z,t.elapsed())
    });
    let mut zs=Vec::with_capacity(n);
    for(i,(z,elapsed))in prepared_z.into_iter().enumerate(){pt[i].sc2_prep+=elapsed;zs.push(z);}
    drop(parties);
    drop(st);
    let h2: L = crate::transport::scalars((0..n).map(|i| lag[i] * masks[i][1].sum()).collect()).into_iter().sum();
    let lambda2 = tr.round(&ZERO, bytes(&[h2])).field();
    assert_ne!(lambda2, L::ZERO);
    claim2 += lambda2 * h2;
    let mut sc2 = Vec::new();
    let mut rp = Vec::new();
    for _ in 0..cfg.sc2_len() {
        let (parents, pairs) = sparse_pairs(&indices);
        let mut agg = [L::ZERO; 3];
        let partials=crate::parallel::parties(&mut zs, |i,z|{let t=Instant::now();let v=sparse_round(&weights,z,&pairs);let q=masks[i][1].round(&rp);(std::array::from_fn::<_,3,_>(|u|mu2[i]*v[u]+lambda2*lag[i]*q[u]),t.elapsed())});
        for(i,(_,elapsed))in partials.iter().enumerate(){pt[i].sc2+=*elapsed;}
        for v in crate::transport::arrays(partials.into_iter().map(|x|x.0).collect()){for u in 0..3{agg[u]+=v[u];}}
        assert_eq!(agg[0] + agg[1], claim2, "SC2");
        let r = tr.round(&ZERO, bytes(&agg)).field();
        assert_ne!(r, L::ONE, "SC2 excluded challenge");
        claim2 = interp(&agg, r);
        sc2.push(agg);
        rp.push(r);
        weights = sparse_fold(&weights, &pairs, r);
        let durations=crate::parallel::parties(&mut zs, |_,z|{let t=Instant::now();*z=sparse_fold(z,&pairs,r);t.elapsed()});
        for(i,elapsed)in durations.into_iter().enumerate(){pt[i].sc2+=elapsed;}
        indices = parents;
    }
    let value: L = crate::transport::scalars((0..n).map(|i| mu2[i] * zs[i][0]).collect()).into_iter().sum();
    let y2: L = crate::transport::scalars((0..n).map(|i| lag[i] * masks[i][1].value(&rp)).collect()).into_iter().sum();
    assert_eq!(claim2, weights[0] * value + lambda2 * y2);
    let matrix_started=Instant::now();
    let matrix_proof=index.map(|i| {
        tr.absorb(b"private matrix endpoint",bytes(&[weights[0], value, y2]));
        crate::sparse_matrix::prove(&i.private,&rcol,&rp,rho,weights[0],&mut tr)
    });
    tm.public_matrix_proof=matrix_started.elapsed();
    let matrix_weight=weights[0];
    let eta = tr.round(&ZERO, bytes(&[value, y2])).field();
    let mut gw = zk::selector_weights(&rx, 3);
    gw.extend(zk::selector_weights(&rp, 2).into_iter().map(|x| eta * x));
    let t = Instant::now();
    let gproof = zk::open_g(&cfg.g, &cfg.gmap, &gw, gprepared, &mut tr);
    tm.g_open = t.elapsed();
    tr.absorb(b"G opening", &encode_pcs(&gproof));
    tm.piop = piop_start.elapsed() - tm.g_open;
    tm.parties = pt;
    let inst = Instance {
        r_h: rp[..8].to_vec(),
        r_a: ry,
        r_b: rp[8..].to_vec(),
        s_x: value,
    };
    tr.absorb(b"main instance", &inst.to_bytes());
    let t = Instant::now();
    let (pcs, _, _) = protocol::open_prepared_in::<H>(&cfg.pcs, &inst, prepared, &mut tr);
    tm.pcs_open = t.elapsed();
    let proof = Proof {
        nonce,
        top,
        h1,
        h2,
        y1,
        y2,
        conversions,
        g: gproof,
        sc1,
        endpoints,
        sc2,
        value,
        pcs,
    };
    let _network_pause=crate::transport::pause();
    let t = Instant::now();
    let matrix=public_proof.zip(matrix_proof).map(|(input,private)|crate::indexed::MatrixProof{public_value:public,input,weight:matrix_weight,private});
    if verify_after {
        if let Some(i)=index {crate::indexed::verify(&i.verifier_key(cfg),&digests,&proof,matrix.as_ref().unwrap()).expect("indexed full verification");}
        else {verify(cfg, &digests, &proof).expect("full spine verification");}
        tm.verify = t.elapsed();
    }
    tm.total = total.elapsed();
    (Run { proof, digests, times: tm },matrix)
}

/// Reads no private witness, row values, server shares, RNG seed, or prover state.
pub fn verify(cfg: &Config, digests: &[[u8; 32]], proof: &Proof) -> Result<(), String> {
    verify_with_statement(cfg, digests, proof, &cfg.statement(digests), MatrixEvaluation::Expanded)
}

pub(crate) enum MatrixEvaluation { Expanded, Structured }

/// Shared direct-verification checks. Only the structured wrapper supplies a new statement.
/// The indexed verifier and its transcript are unchanged.
pub(crate) fn verify_with_statement(cfg: &Config, digests: &[[u8; 32]], proof: &Proof,
    statement: &[u8], evaluation: MatrixEvaluation) -> Result<(), String> {
    if digests.len() != cfg.batch()
        || proof.sc1.len() != cfg.sc1_len()
        || proof.sc2.len() != cfg.sc2_len()
        || proof.pcs.roots.len() != cfg.pcs.params.folds()
        || proof.g.roots.len() != cfg.g.params.folds()
        || proof.conversions.len() != 2
        || proof.conversions.iter().any(|v| v.len() != cfg.ctx.n)
    {
        return Err("shape".into());
    }
    let h = Hasher::<H>::default();
    let mut tr = Transcript::new_global(&h, statement);
    let top = h.hash(&[b"v04-top", &proof.pcs.roots[0], &proof.g.roots[0]]);
    if top != proof.top {
        return Err("top root".into());
    }
    tr.absorb(
        b"initial roots",
        &[proof.pcs.roots[0], proof.g.roots[0]].concat(),
    );
    let mut c = tr.round(&top, &proof.nonce);
    let tau: Vec<_> = (0..cfg.sc1_len()).map(|_| c.field()).collect();
    let lambda1 = tr.round(&ZERO, bytes(&[proof.h1])).field();
    if lambda1 == L::ZERO {
        return Err("lambda1 excluded".into());
    }
    let mut claim = lambda1 * proof.h1;
    let mut rx = Vec::new();
    for (round, s) in proof.sc1.iter().enumerate() {
        if round == cfg.circuit.base.log_m0 + cfg.groups.trailing_zeros() as usize {
            tr.absorb(b"conversions", bytes(&proof.conversions.concat()));
        }
        if s[0] + s[1] != claim {
            return Err("SC1 sum".into());
        }
        let r = tr.round(&ZERO, bytes(s)).field();
        if r == L::ONE { return Err("SC1 excluded challenge".into()); }
        claim = interp(s, r);
        rx.push(r);
    }
    let v = proof.endpoints;
    if claim != eq_eval(&tau, &rx) * (v[0] * v[1] + v[2]) + lambda1 * proof.y1 {
        return Err("SC1 endpoint".into());
    }
    let nvcol = cfg.circuit.base.log_m0 + cfg.groups.trailing_zeros() as usize;
    let (rcol, ry) = rx.split_at(nvcol);
    let mut ep = v.to_vec();
    ep.push(proof.y1);
    let mut c = tr.round(&ZERO, bytes(&ep));
    let rho: [L; 3] = std::array::from_fn(|_| c.field());
    enum Weights {
        Expanded(Vec<usize>, Vec<L>, L),
        Structured(crate::sha_spartan::MatrixWeights),
    }
    let weights = match evaluation {
        MatrixEvaluation::Expanded => {
            let (indices, w, public) = cfg.weights(rcol, ry, rho, digests);
            Weights::Expanded(indices, w, public)
        }
        MatrixEvaluation::Structured => Weights::Structured(cfg.matrix_weights(rcol, ry, rho, digests)),
    };
    let public = match &weights {
        Weights::Expanded(_, _, public) => *public,
        Weights::Structured(weights) => weights.public,
    };
    let mut claim = rho.iter().zip(v).map(|(&a, b)| a * b).sum::<L>() + public;
    let lambda2 = tr.round(&ZERO, bytes(&[proof.h2])).field();
    if lambda2 == L::ZERO {
        return Err("lambda2 excluded".into());
    }
    claim += lambda2 * proof.h2;
    let mut rp = Vec::new();
    for s in &proof.sc2 {
        if s[0] + s[1] != claim {
            return Err("SC2 sum".into());
        }
        let r = tr.round(&ZERO, bytes(s)).field();
        if r == L::ONE { return Err("SC2 excluded challenge".into()); }
        claim = interp(s, r);
        rp.push(r);
    }
    let wr = match weights {
        Weights::Expanded(indices, w, _) => {
            let eh = eq_expand(&rp[..8]);
            let ex = eq_expand(&rp[8..]);
            indices.iter().zip(w).map(|(&i, a)| a * eh[i % D] * ex[i / D]).sum()
        }
        Weights::Structured(weights) => weights.evaluate(&cfg.inner, &rp),
    };
    if claim != wr * proof.value + lambda2 * proof.y2 {
        return Err("SC2 endpoint".into());
    }
    let eta = tr.round(&ZERO, bytes(&[proof.value, proof.y2])).field();
    let mut gw = zk::selector_weights(&rx, 3);
    gw.extend(zk::selector_weights(&rp, 2).into_iter().map(|x| eta * x));
    zk::verify_g(
        &cfg.g,
        &cfg.gmap,
        &gw,
        proof.y1 + eta * proof.y2,
        &proof.g,
        &mut tr,
    )?;
    tr.absorb(b"G opening", &encode_pcs(&proof.g));
    let inst = Instance {
        r_h: rp[..8].to_vec(),
        r_a: ry.to_vec(),
        r_b: rp[8..].to_vec(),
        s_x: proof.value,
    };
    tr.absorb(b"main instance", &inst.to_bytes());
    protocol::verify_in::<H>(&cfg.pcs, &inst, &proof.pcs, &mut tr, zk::BIT_ROLE)?;
    Ok(())
}

pub(crate) fn encode_pcs(p: &PcsProof) -> Vec<u8> {
    let mut v = Vec::new();
    for r in &p.roots {
        v.extend_from_slice(r);
    }
    v.extend_from_slice(&p.tail_root);
    v.extend_from_slice(bytes(&[p.xi]));
    v.extend_from_slice(bytes(&p.t));
    v.extend_from_slice(bytes(&[p.h_omega]));
    for &(a, b) in &p.coeffs {
        v.extend_from_slice(bytes(&[a, b]));
    }
    for (t, s) in p.tails.iter().zip(&p.tail_salts) {
        v.extend_from_slice(bytes(t));
        v.extend_from_slice(s);
    }
    for q in &p.openings {
        for o in q {
            v.extend_from_slice(bytes(&o.values));
            v.extend_from_slice(&o.salt);
            for h in &o.path {
                v.extend_from_slice(h);
            }
        }
    }
    v
}
pub(crate) struct Reader<'a>(pub(crate) &'a [u8]);
impl<'a> Reader<'a> {
    pub(crate) fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.0.len() < n {
            return Err("truncated v04 proof".into());
        }
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Ok(a)
    }
    pub(crate) fn hash(&mut self) -> Result<Hash, String> {
        Ok(self.take(32)?.try_into().unwrap())
    }
    pub(crate) fn field(&mut self) -> Result<L, String> {
        let b = self.hash()?;
        Ok(from_words([
            u128::from_le_bytes(b[..16].try_into().unwrap()),
            u128::from_le_bytes(b[16..].try_into().unwrap()),
        ]))
    }
    pub(crate) fn fields(&mut self, n: usize) -> Result<Vec<L>, String> {
        (0..n).map(|_| self.field()).collect()
    }
    pub(crate) fn pcs(&mut self, s: &Setup, frontend: bool) -> Result<PcsProof, String> {
        let len = u64::from_le_bytes(self.take(8)?.try_into().unwrap());
        let mut r = Reader(self.take(usize::try_from(len).map_err(|_| "section length")?)?);
        let p = &s.params;
        let roots = (0..p.folds()).map(|_| r.hash()).collect::<Result<_, _>>()?;
        let tail_root = r.hash()?;
        let xi = r.field()?;
        let t = r.fields(if frontend { D } else { 0 })?;
        let h_omega = r.field()?;
        let coeffs = (0..p.folds())
            .map(|_| Ok((r.field()?, r.field()?)))
            .collect::<Result<_, String>>()?;
        let (mut tails, mut tail_salts) = (vec![], vec![]);
        for _ in 0..p.n_parties {
            tails.push(r.fields(1 << p.tau)?);
            tail_salts.push(r.hash()?);
        }
        let mut openings = vec![];
        for _ in 0..p.gamma {
            let mut q = vec![];
            for j in 0..p.folds() {
                let values = r.fields(2)?.try_into().unwrap();
                let salt = r.hash()?;
                let path = (0..p.log_n_parties() + p.m() - j - 1)
                    .map(|_| r.hash())
                    .collect::<Result<_, _>>()?;
                q.push(protocol::Opening { values, salt, path });
            }
            openings.push(q);
        }
        if !r.0.is_empty() {
            return Err("PCS section trailing bytes".into());
        }
        Ok(PcsProof {
            roots,
            tail_root,
            xi,
            t,
            h_omega,
            coeffs,
            tails,
            tail_salts,
            openings,
        })
    }
}
impl Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut v = b"B2SHA007".to_vec();
        v.extend_from_slice(&self.nonce);
        v.extend_from_slice(&self.top);
        v.extend_from_slice(bytes(&[self.h1, self.h2, self.y1, self.y2]));
        for x in &self.sc1 {
            v.extend_from_slice(bytes(x));
        }
        v.extend_from_slice(bytes(&self.endpoints));
        for x in &self.sc2 {
            v.extend_from_slice(bytes(x));
        }
        v.extend_from_slice(bytes(&[self.value]));
        for x in &self.conversions {
            v.extend_from_slice(bytes(x));
        }
        for p in [&self.g, &self.pcs] {
            let b = encode_pcs(p);
            v.extend_from_slice(&(b.len() as u64).to_le_bytes());
            v.extend_from_slice(&b);
        }
        v
    }
    pub fn from_bytes(cfg: &Config, b: &[u8]) -> Result<Self, String> {
        Self::from_shape(cfg.sc1_len(),cfg.sc2_len(),cfg.ctx.n,&cfg.g,&cfg.pcs,b)
    }
    pub(crate) fn from_shape(sc1:usize,sc2:usize,n:usize,gsetup:&Setup,psetup:&Setup,b:&[u8])->Result<Self,String>{
        let mut r = Reader(b);
        if r.take(8)? != b"B2SHA007" {
            return Err("expected global-d BLAKE3 proof (B2SHA007); historical SHA-hashed proofs are incompatible".into());
        }
        let nonce = r.hash()?;
        let top = r.hash()?;
        let h1 = r.field()?;
        let h2 = r.field()?;
        let y1 = r.field()?;
        let y2 = r.field()?;
        let sc1 = (0..sc1)
            .map(|_| Ok(r.fields(4)?.try_into().unwrap()))
            .collect::<Result<_, String>>()?;
        let endpoints = r.fields(3)?.try_into().unwrap();
        let sc2 = (0..sc2)
            .map(|_| Ok(r.fields(3)?.try_into().unwrap()))
            .collect::<Result<_, String>>()?;
        let value = r.field()?;
        let conversions = (0..2)
            .map(|_| r.fields(n))
            .collect::<Result<_, _>>()?;
        let g = r.pcs(gsetup, false)?;
        let pcs = r.pcs(psetup, true)?;
        if !r.0.is_empty() {
            return Err("v04 trailing bytes".into());
        }
        Ok(Self {
            nonce,
            top,
            h1,
            h2,
            y1,
            y2,
            sc1,
            endpoints,
            sc2,
            value,
            conversions,
            g,
            pcs,
        })
    }
}
/// Payload accounting for the ideal execution, not a network byte/latency measurement.
pub fn communication(cfg: &Config, p: &Proof) -> (usize, usize, usize, usize) {
    let n = cfg.ctx.n;
    let field = 32;
    let client = n * cfg.groups * (cfg.circuit.private_len + 3 * cfg.circuit.base.m0()) * 16
        + n * (cfg.pcs.params.n() - cfg.pcs.layout.pad.len()) * field;
    let preprocessing = n
        * (cfg.pcs.layout.pad.len() + cfg.g.params.n() + cfg.gmap.len() + 2 * (1 + cfg.ctx.k) + 1)
        * field;
    let mut aggregate = n * field * (4 * cfg.sc1_len() + 3 * cfg.sc2_len() + 2 + 4 + 2 + 1 + 2);
    for (s, p, front) in [(&cfg.g, &p.g, false), (&cfg.pcs, &p.pcs, true)] {
        aggregate +=
            n * field * (p.roots.len() + 2 * p.coeffs.len() + 2 + if front { D + 1 } else { 0 });
        aggregate += p.tails.iter().map(|v| v.len() * field + 32).sum::<usize>();
        aggregate += p
            .openings
            .iter()
            .flatten()
            .map(|o| 96 + 32 * (o.path.len() - s.params.log_n_parties()))
            .sum::<usize>();
    }
    (client, preprocessing, aggregate, p.to_bytes().len())
}
#[cfg(test)]
mod tests {
    use super::*;
    // Exercise the real transcript and both verifier entry points, not a predicate mock.
    #[test]
    fn outer_raw_one_is_rejected_without_retry() {
        use crate::fs::testing::with_field;
        for indexed in [false,true] {
            // The direct legacy entry point is SHA-specific; indexed supports synthetic circuits.
            let cfg=if indexed {Config::synthetic(8,1,16,3,32)} else {Config::new(8,1,16,3)};
            let index=crate::indexed::Index::new(&cfg,16);
            let idx=if indexed {Some(&index)} else {None};
            let (run,matrix)=prove_core(&cfg,1234,StdRng::seed_from_u64(991),idx);
            let verify=||if indexed {crate::indexed::verify(&index.verifier_key(&cfg),&run.digests,&run.proof,matrix.as_ref().unwrap())}else{super::verify(&cfg,&run.digests,&run.proof)};
            verify().unwrap();
            let row_end=cfg.circuit.base.log_m0+cfg.groups.trailing_zeros() as usize;
            let targets=[(bytes(&run.proof.sc1[0]),"SC1 excluded challenge"),
                (bytes(&run.proof.sc1[row_end-1]),"SC1 excluded challenge"),
                (bytes(&run.proof.sc1[row_end]),"SC1 excluded challenge"),
                (bytes(&run.proof.sc2[0]),"SC2 excluded challenge"),
                (bytes(run.proof.sc2.last().unwrap()),"SC2 excluded challenge")];
            for (message,error) in targets {
                assert_eq!(with_field(message,L::ONE,verify),Err(error.into()));
                let abort=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||with_field(message,L::ONE,||prove_core(&cfg,1234,StdRng::seed_from_u64(991),idx))));
                let payload=abort.err().expect("prover must abort on raw one");
                let text=payload.downcast_ref::<String>().map(String::as_str).or_else(||payload.downcast_ref::<&str>().copied()).unwrap_or("");
                assert!(text.contains(error),"wrong abort: {text}");
            }
        }
    }
    #[test]
    fn outer_raw_zero_remains_valid() {
        use crate::fs::testing::with_field;
        for indexed in [false,true] {
            // The direct legacy entry point is SHA-specific; indexed supports synthetic circuits.
            let cfg=if indexed {Config::synthetic(8,1,16,3,32)} else {Config::new(8,1,16,3)};
            let index=crate::indexed::Index::new(&cfg,16);
            let idx=if indexed {Some(&index)} else {None};
            let (base,_)=prove_core(&cfg,1234,StdRng::seed_from_u64(991),idx);
            for message in [bytes(&base.proof.sc1[0]),bytes(&base.proof.sc2[0])] {
                let(run,matrix)=with_field(message,L::ZERO,||prove_core(&cfg,1234,StdRng::seed_from_u64(991),idx));
                with_field(message,L::ZERO,||if indexed {crate::indexed::verify(&index.verifier_key(&cfg),&run.digests,&run.proof,matrix.as_ref().unwrap())}else{super::verify(&cfg,&run.digests,&run.proof)}).unwrap();
            }
        }
    }
    #[cfg(feature="parallel")]
    #[test]
    fn indexed_single_worker_matches_32_workers() {
        let cfg=Config::synthetic(32,1,16,3,32);
        let index=crate::indexed::Index::new(&cfg,16);
        let run=|threads|rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap().install(|| {
            let(p,m)=prove_core(&cfg,21,StdRng::seed_from_u64(991),Some(&index));
            crate::indexed_codec::encode_proof(&p.proof,&m.unwrap())
        });
        let serial=run(1);assert_eq!(serial,run(32));
        let wire=rayon::ThreadPoolBuilder::new().num_threads(32).build().unwrap().install(|| {
            crate::transport::start(32);
            let(p,m)=prove_core(&cfg,21,StdRng::seed_from_u64(991),Some(&index));
            let stats=crate::transport::stop();assert!(stats.up>0&&stats.down>0);
            crate::indexed_codec::encode_proof(&p.proof,&m.unwrap())
        });
        assert_eq!(serial,wire);
    }
    #[test]
    fn full_v04_roundtrip_and_bindings() {
        let cfg = Config::new(8, 1, 16, 3);
        let (start, row) = cfg.circuit.mask_start.unwrap();
        for g in 0..cfg.groups {
            for b in 0..4 {
                let a = cfg.map[g * cfg.circuit.base.n0() + start + b * 1024];
                assert_eq!(a % 1024, 0);
                for j in 0..1024 {
                    assert_eq!(
                        cfg.map[g * cfg.circuit.base.n0() + start + b * 1024 + j],
                        a + j
                    );
                }
            }
        }
        let mut addresses = cfg.map.clone();
        addresses.sort_unstable();
        assert!(addresses.windows(2).all(|a| a[0] < a[1]));
        assert!(row + 3072 <= cfg.circuit.base.m0());
        let run = prove_with_rng(&cfg, 1234, StdRng::seed_from_u64(991));
        let b = run.proof.to_bytes();
        let mut legacy = b.clone();
        legacy[..8].copy_from_slice(b"B2SHA004");
        assert!(Proof::from_bytes(&cfg, &legacy).is_err());
        let p = Proof::from_bytes(&cfg, &b).unwrap();
        verify(&cfg, &run.digests, &p).unwrap();
        for kind in 0..8 {
            let mut bad = p.clone();
            match kind {
                0 => bad.nonce[0] ^= 1,
                1 => bad.g.roots[0][0] ^= 1,
                2 => bad.h1 += L::ONE,
                3 => bad.y2 += L::ONE,
                4 => bad.conversions[0][0] += L::ONE,
                5 => bad.g.h_omega += L::ONE,
                6 => bad.g.tails[0][0] += L::ONE,
                _ => bad.pcs.tails[0][0] += L::ONE,
            };
            assert!(verify(&cfg, &run.digests, &bad).is_err(), "mutation {kind}");
        }
        assert!(Proof::from_bytes(&cfg, &b[..b.len() - 1]).is_err());
        let mut more = b.clone();
        more.push(0);
        assert!(Proof::from_bytes(&cfg, &more).is_err());
        let (mut z, mut rows, _) = cfg.circuit.witness(&[0; 32]);
        let mut r = StdRng::seed_from_u64(1);
        cfg.circuit.randomize_masks(&mut z, &mut rows, &mut r);
        assert!(
            rows[0]
                .iter()
                .zip(&rows[1])
                .zip(&rows[2])
                .all(|((&a, &b), &c)| a & b == c)
        );
        let other = prove_with_rng(&cfg, 1234, StdRng::seed_from_u64(992));
        assert_eq!(run.digests, other.digests);
        assert_ne!(run.proof.pcs.roots[0], other.proof.pcs.roots[0]);
        assert_ne!(run.proof.g.roots[0], other.proof.g.roots[0]);
        assert_ne!(run.proof.nonce, other.proof.nonce);
    }
}
