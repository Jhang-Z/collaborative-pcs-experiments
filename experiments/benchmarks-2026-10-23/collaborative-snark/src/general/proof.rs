//! Arbitrary row-slot / witness-slot R1CS. No equality of slot indices is assumed.
#[cfg(test)]
use std::time::Instant;
use binius_hash::Blake3HashSuite as H;
use binius_field::arithmetic_traits::InvertOrZero;
use rand::Rng;
use crate::{field::{basis,from_b,eq_expand,Field,L,Random,D}, merkle::{Hash,Hasher},
    protocol, sha_spartan::{sparse_pairs,sparse_fold,sparse_round},
    sha_zk, spartan::{Ctx,eq_eval,fold_l,interp,round_l},
    setup::{Setup,Instance,Witness}, fs::Transcript, zk::{self,Selector}};
use super::{Circuit,distributed::{Runtime,Vector,bounds},sparse,onehot,public_input};
use std::{cell::RefCell,sync::Arc};

const ZERO:Hash=[0;32];
fn bytes(v:&[L])->&[u8] {bytemuck::cast_slice(v)}
fn fields(tr:&mut Transcript<'_,H>,v:&[L])->L {tr.round(&ZERO,bytes(v)).field()}
fn bool_field(b:bool)->L {if b{L::ONE}else{L::ZERO}}

pub struct Config {
    pub geometry:sha_zk::Config,
    pub private:onehot::Index,
    pub public:public_input::Index,
    pub circuit_hash:Hash,
    runtime:RefCell<Runtime>,
    checkpoint:usize,
    binding:Vec<u8>,
    lag:Vec<L>,
    inverse_lag:Vec<L>,
    omega:Vec<L>,
}
pub struct VerifierKey {
    pub n:usize,
    pub row_bits:usize,
    pub physical_bits:usize,
    pub pcs:Setup,
    pub g:Setup,
    pub gmap:Vec<usize>,
    pub private:onehot::Key,
    pub public:crate::public_pcs::Key,
    pub circuit_hash:Hash,
}
pub struct MatrixProof {pub public_value:L,pub input:public_input::Proof,pub weight:L,pub private:onehot::Proof}
impl MatrixProof {pub fn encode(&self)->Vec<u8>{let mut b=bytes(&[self.public_value,self.weight]).to_vec();let input=self.input.encode();b.extend((input.len() as u64).to_le_bytes());b.extend(input);b.extend(self.private.encode());b}}
pub struct Proof {
    pub core:sha_zk::Proof,
    /// The independent third double sharing, between physical and slot SC2 rounds.
    pub column_conversion:Vec<L>,
    pub matrix:MatrixProof,
}
impl Config {
    #[cfg(test)] pub fn new(c:&Circuit,n:usize,gamma:usize,tau:usize)->Result<Self,String> {Self::new_block(c,n,gamma,tau,3)}
    pub fn new_block(c:&Circuit,n:usize,gamma:usize,tau:usize,block_bits:usize)->Result<Self,String> {
        if !matches!(block_bits,3|5){return Err("index block bits must be 3 or 5".into());}
        let groups=c.groups(n).map_err(|e|e.to_string())?;
        let mut geometry=sha_zk::Config::synthetic(n,groups,gamma,tau,c.layout_gates);
        if geometry.circuit.base.n0()!=c.base_bits||geometry.circuit.base.m0()!=c.base_rows {
            return Err("general circuit layout mismatch".into());
        }
        let total_sc2=geometry.sc2_len()+geometry.ctx.k.ilog2() as usize;
        (geometry.g,geometry.gmap)=zk::g_setup(n,gamma,tau,4*geometry.sc1_len()+3*total_sc2);
        let row_bits=c.rows().ilog2() as usize;
        let physical_bits=geometry.sc2_len();
        let local_bits=c.bits()/geometry.ctx.k;
        let (private,public)=c.entries();
        let private=private.into_iter().map(|(a,r,col)| {
            let slot=col/local_bits;
            (a,r,(slot<<physical_bits)|geometry.map[col%local_bits])
        }).collect();
        let mut runtime=Runtime::new(n);
        let column_map=sparse::ColumnMap::new(physical_bits,geometry.ctx.k,&geometry.map);
        let private=onehot::Index::new(&mut runtime,row_bits,physical_bits+geometry.ctx.k.ilog2() as usize,private,column_map,gamma,tau,block_bits);let public=public_input::Index::new(&mut runtime,row_bits,&public,gamma);
        runtime.flush();let checkpoint=runtime.checkpoint();
        let lag=geometry.ctx.lag_eta0();let inverse_lag=lag.iter().map(|&v|v.invert_or_zero()).collect();
        let omega=geometry.ctx.lag_n.iter().map(|row|row.iter().copied().sum()).collect();
        let mut cfg=Self {private,public,circuit_hash:Hasher::<H>::default().hash(&[b"general global circuit v1",&serde_json::to_vec(c).unwrap()]),geometry,runtime:RefCell::new(runtime),checkpoint,binding:vec![],lag,inverse_lag,omega};
        cfg.binding=cfg.verifier_key().binding();Ok(cfg)
    }
    pub fn actor_stats(&self)->Vec<super::distributed::Stats> {self.runtime.borrow_mut().snapshot()}
    pub fn parameter_record(&self)->serde_json::Value {
        let private=[&self.geometry.pcs.params,&self.geometry.g.params];
        let index=&self.private.key;
        let r=self.geometry.sc1_len()+index.col_bits+private.iter().map(|p|p.folds()).sum::<usize>()+
            index.entry_bits+1+index.block_bits+index.selector_bits()+index.params.mu()+11+(self.public.key.log-1);
        let excluded=2+self.geometry.sc1_len()+index.col_bits+
            private.iter().chain(std::iter::once(&&index.params)).map(|p|3*p.cstar()+1+p.folds()).sum::<usize>()+(self.public.key.log-3);
        assert!(r<=65536&&excluded<=65536&&self.geometry.sc1_len()<=64&&self.private.key.col_bits<=64);
        serde_json::json!({"expected_challenge_stages":r,"excluded_raw_coordinates":excluded,"nu":10,"d":256,
            "row_bits":self.geometry.sc1_len(),"column_bits":self.private.key.col_bits,
            "private_setups":private.iter().map(|p|{assert!(p.ell<=40);serde_json::json!({"ell":p.ell,"beta":p.beta,"gamma":p.gamma,"tau":p.tau,"cstar":p.cstar(),"folds":p.folds(),"n1":p.n_parties*(1usize<<(p.m()-1))})}).collect::<Vec<_>>(),
            "public_columns":{"log":self.public.key.log,"batch_size":6,"queries":self.public.key.queries,"largest_n1":2usize<<self.public.key.log},
            "public_indices":[],"onehot_index":{"entry_bits":index.entry_bits,"block_bits":index.block_bits,"blocks":index.blocks(),"selector_bits":index.selector_bits(),"outer_degree":index.blocks()+1,"ell":index.params.ell,"beta":index.params.beta,"gamma":index.params.gamma,"tau":index.params.tau,"cstar":index.params.cstar(),"folds":index.params.folds(),"n1":index.params.n_parties*(1usize<<(index.params.m()-1))}})
    }

    pub fn verifier_key(&self)->VerifierKey {
        VerifierKey {n:self.geometry.ctx.n,row_bits:self.geometry.sc1_len(),
            physical_bits:self.geometry.sc2_len(),
            pcs:Setup::verifier_compact(self.geometry.pcs.params.clone()),g:Setup::verifier_compact(self.geometry.g.params.clone()),
            gmap:self.geometry.gmap.clone(),private:self.private.key.clone(),public:self.public.key.clone(),
            circuit_hash:self.circuit_hash}
    }
}
impl VerifierKey {
    pub fn slot_bits(&self)->usize {self.pcs.params.k().ilog2() as usize}
    pub fn binding(&self)->Vec<u8> {super::codec::encode_key(self)}
    fn transcript<'a>(&self,hasher:&'a Hasher<H>,public:&[bool;2],nonce:&Hash,top:&Hash,groot:&Hash)->Transcript<'a,H> {
        transcript(&self.binding(),hasher,public,nonce,top,groot)
    }
}
fn transcript<'a>(binding:&[u8],hasher:&'a Hasher<H>,public:&[bool;2],nonce:&Hash,top:&Hash,groot:&Hash)->Transcript<'a,H>{
        let mut tr=Transcript::new_global(hasher,b"general collaborative binary R1CS onehot v1");
        tr.absorb(b"verifier key",binding);
        tr.absorb(b"public statement",&public.map(u8::from));
        tr.absorb(b"session nonce",nonce);tr.absorb(b"witness root",top);tr.absorb(b"G root",groot);tr
}

/// Independent ideal F_dsh material, delivered before its online disclosure.
struct DoubleSharing {packed:Vec<L>,ordinary:Vec<Vec<L>>}
fn prepare_conversion(ctx:&Ctx,rng:&mut impl Rng)->DoubleSharing {
    let r:Vec<L>=(0..ctx.k).map(|_|L::random(&mut *rng)).collect();
    let packed=ctx.share_packed(&r,rng);
    let columns:Vec<_>=r.iter().map(|&v|ctx.share_sss(v,rng)).collect();
    let ordinary=(0..ctx.n).map(|i|(0..ctx.k).map(|s|columns[s][i]).collect()).collect();
    DoubleSharing{packed,ordinary}
}
fn convert(ctx:&Ctx,packed:&[L],mut material:DoubleSharing)->(Vec<L>,Vec<Vec<L>>) {
    crate::parallel::parties(&mut material.packed,|i,v|*v+=packed[i]);
    let masked=crate::transport::scalars(material.packed);
    let delta=ctx.open_packed_fft(&masked);crate::transport::broadcast(bytes(&delta));
    crate::parallel::parties(&mut material.ordinary,|_,row|for(v,&d)in row.iter_mut().zip(&delta){*v+=d;});
    (masked,material.ordinary)
}
fn aggregate(n:usize,f:impl Fn(usize)->L+Sync+Send)->L {
    let mut partials=vec![L::ZERO;n];crate::parallel::parties(&mut partials,|i,v|*v=f(i));
    crate::transport::scalars(partials).into_iter().sum()
}

fn packed_weights(rt:&mut Runtime,weights:Vector,k:usize,physical_bits:usize,map:&[usize])->Vector {
    let physical=map.len();let kp=2*k;let local=map.len();let n=rt.n;
    let _=physical_bits;
    assert_eq!(physical%n,0);
    let transposed=rt.reindex(weights,physical*kp,move|j,x,out|out.push(((j%physical)*kp+j/physical,x)),false);
    
    let output=Vector{id:rt.id(),len:n*local};
    rt.run_effect(move|w| {
        let (lo,_)=bounds(transposed.len,w.n,w.rank);assert_eq!(lo%kp,0);
        let code=crate::code::ColCode::new(kp.ilog2() as usize);let mut records=vec![];
        for (j,values) in w.arrays[&transposed.id].chunks_exact(kp).enumerate() {
            let logical=lo/kp+j; {
                let polynomial=code.interpolate(values,0);let shares=code.evaluate(&polynomial);
                for party in 0..n {records.push((party*local+logical,shares[kp+party]));}
            }
        }
        w.route_dense(output.id,output.len,records,output.len);vec![]
    });rt.release(&[transposed]);output
}

pub fn prove(cfg:&Config,circuit:&Circuit,witness:&[bool],public:&[bool;2],rng:&mut impl Rng)->Proof {
    let _encoding=crate::code::sequential_encoding();
    let preparation=crate::execution_trace::pause();
    circuit.check(witness,public).expect("valid general circuit witness");
    let mut runtime=cfg.runtime.borrow_mut();
    runtime.begin_proof(cfg.checkpoint);
    let index_prepared=cfg.private.take_prepared();
    let cfg0=&cfg.geometry;
    let ctx=&cfg0.ctx;
    let (n,k)=(ctx.n,ctx.k);
    let local_rows=circuit.rows()/k;
    let local_bits=circuit.bits()/k;
    let local_row_bits=local_rows.ilog2() as usize;
    let physical_bits=cfg0.sc2_len();
    let total_sc2=physical_bits+ctx.k.ilog2() as usize;
    let row_values=circuit.row_values(witness,public);
    let selectors=[Selector::random(cfg0.sc1_len(),3,rng),Selector::random(total_sc2,2,rng)];
    let mut masks:Vec<[Selector;2]>=(0..n).map(|_|[
        Selector{polys:vec![vec![L::ZERO;4];cfg0.sc1_len()]},
        Selector{polys:vec![vec![L::ZERO;3];total_sc2]}]).collect();
    for a in 0..2 {for j in 0..selectors[a].polys.len() {for u in 0..selectors[a].polys[j].len() {
        let sh=ctx.share_sss(selectors[a].polys[j][u],rng);
        for i in 0..n {masks[i][a].polys[j][u]=sh[i];}
    }}}
    let mut conversion_material:Vec<_>=(0..3).map(|_|prepare_conversion(ctx,rng)).collect();
    let column_material=conversion_material.pop().unwrap();
    let column_material=column_material.ordinary.into_iter().zip(column_material.packed).map(|(q,r)|{let mut row=vec![r];row.extend(q);row}).collect();
    let column_material=runtime.load_parties(column_material);
    let coefficients:Vec<L>=selectors.iter().flat_map(Selector::coefficients).collect();
    let gprepared=protocol::prepare_random::<H>(&cfg0.g,&zk::g_witness(&cfg0.g,&cfg0.gmap,&coefficients),rng,zk::G_ROLE);
    let mut rows:Vec<[Vec<L>;3]>=(0..n).map(|_|std::array::from_fn(|_|vec![L::ZERO;local_rows])).collect();
    let mut zs=vec![vec![L::ZERO;local_bits];n];
    let mut buf=vec![crate::field::B::ZERO;n];
    for j in 0..local_bits {
        ctx.share_bits(|s|witness[s*local_bits+j],rng,&mut buf);
        for i in 0..n {zs[i][j]=from_b(buf[i]);}
    }
    for a in 0..3 {for j in 0..local_rows {
        ctx.share_bits(|s|row_values[a][s*local_rows+j],rng,&mut buf);
        for i in 0..n {rows[i][a][j]=from_b(buf[i]);}
    }}
    let cols=cfg0.pcs.params.n();
    let mut wit=Witness{table:vec![L::ZERO;k*cols]};
    for s in 0..k {for j in 0..local_bits {if witness[s*local_bits+j] {
        let pos=cfg0.map[j];wit.table[s*cols+pos/D]+=basis(pos%D);
    }}}
    for m in cfg0.pcs.layout.masks.iter().flatten() {wit.table[m.y*cols+m.x]=L::random(&mut *rng);}
    let prepared=protocol::prepare_random::<H>(&cfg0.pcs,&wit,rng,zk::BIT_ROLE);
    let top=prepared.root;
    let mut zs=runtime.load_parties(zs);
    let mask_shares=runtime.load_parties(masks.iter().map(|m|m[1].coefficients()).collect());
    runtime.seal();runtime.flush();
    drop(preparation);
    
    let nonce=Hasher::<H>::default().hash(&[b"general session",bytes(&[L::random(&mut *rng)])]);
    let hasher=Hasher::<H>::default();
    let mut tr=transcript(&cfg.binding,&hasher,public,&nonce,&top,&gprepared.root);
    let lag=&cfg.lag;
    let h1=aggregate(n,|i|lag[i]*masks[i][0].sum());
    let mut challenges=tr.round(&ZERO,bytes(&[h1]));
    let lambda1=challenges.field();
    assert_ne!(lambda1,L::ZERO,"general lambda1 excluded");
    let tau:Vec<L>=(0..cfg0.sc1_len()).map(|_|challenges.field()).collect();
    let mut equality=vec![[vec![],vec![]];n];
    crate::parallel::parties(&mut equality,|_,e|{e[0]=eq_expand(&tau[..local_row_bits]);e[1]=eq_expand(&tau[local_row_bits..]);});
    let mut mu=vec![L::ZERO;n];crate::parallel::parties(&mut mu,|i,v|*v=(0..k).map(|s|equality[i][1][s]*ctx.lag_n[i][s]).sum());
    let mut claim=lambda1*h1;
    let mut sc1=vec![];let mut rx=vec![];
    for _ in 0..local_row_bits {
        let partials=crate::parallel::parties(&mut rows,|i,state| {
            let v=round_l(&equality[i][0],&state[0],&state[1],&state[2]);let q=masks[i][0].round(&rx);
            std::array::from_fn::<_,4,_>(|u|mu[i]*v[u]+lambda1*lag[i]*q[u])
        });
        let mut agg=[L::ZERO;4];for v in crate::transport::arrays(partials) {for u in 0..4 {agg[u]+=v[u];}}
        assert_eq!(agg[0]+agg[1],claim,"general SC1 columns");
        let r=fields(&mut tr,&agg);assert_ne!(r,L::ONE,"general SC1 excluded challenge");claim=interp(&agg,r);sc1.push(agg);rx.push(r);
        crate::parallel::parties(&mut equality,|_,e|e[0]=fold_l(&e[0],r));
        crate::parallel::parties(&mut rows,|_,state|for v in state {*v=fold_l(v,r);});
    }
    let mut conversions=vec![];
    let mut sss:Vec<[Vec<L>;3]>=(0..n).map(|_|std::array::from_fn(|_|vec![L::ZERO;k])).collect();
    for a in 0..2 {
        let packed:Vec<_>=rows.iter().map(|v|v[a][0]).collect();
        let (masked,ordinary)=convert(ctx,&packed,conversion_material.remove(0));conversions.push(masked.clone());
        for (state,values) in sss.iter_mut().zip(ordinary) {state[a]=values;}
        tr.absorb(b"SC1 conversion",bytes(&masked));
    }
    let inverse_lag=&cfg.inverse_lag;
    crate::parallel::parties(&mut sss,|i,state|for s in 0..k {state[2][s]=ctx.lag_n[i][s]*rows[i][2][0]*inverse_lag[i];});
    for _ in 0..ctx.k.ilog2() as usize {
        let partials=crate::parallel::parties(&mut sss,|i,state| {
            let v=round_l(&equality[i][1],&state[0],&state[1],&state[2]);let q=masks[i][0].round(&rx);
            std::array::from_fn::<_,4,_>(|u|lag[i]*(equality[i][0][0]*v[u]+lambda1*q[u]))
        });
        let mut agg=[L::ZERO;4];for v in crate::transport::arrays(partials) {for u in 0..4 {agg[u]+=v[u];}}
        assert_eq!(agg[0]+agg[1],claim,"general SC1 slots");
        let r=fields(&mut tr,&agg);assert_ne!(r,L::ONE,"general SC1 excluded challenge");claim=interp(&agg,r);sc1.push(agg);rx.push(r);
        crate::parallel::parties(&mut equality,|_,e|e[1]=fold_l(&e[1],r));
        crate::parallel::parties(&mut sss,|_,state|for v in state {*v=fold_l(v,r);});
    }
    let mut opened=[L::ZERO;4];
    let mut contributions=vec![[L::ZERO;4];n];
    crate::parallel::parties(&mut contributions,|i,v|*v=[lag[i]*sss[i][0][0],lag[i]*sss[i][1][0],lag[i]*sss[i][2][0],lag[i]*masks[i][0].value(&rx)]);
    for row in crate::transport::arrays(contributions) {
        for(x,y)in opened.iter_mut().zip(row){*x+=y;}
    }
    let endpoints=[opened[0],opened[1],opened[2]];let y1=opened[3];
    assert_eq!(claim,eq_eval(&tau,&rx)*(endpoints[0]*endpoints[1]+endpoints[2])+lambda1*y1);
    let mut ep=endpoints.to_vec();ep.push(y1);
    let mut challenges=tr.round(&ZERO,bytes(&ep));let rho=std::array::from_fn(|_|challenges.field());
    let public_input=public.map(bool_field);
    let (public_value,input)=public_input::prove(&mut runtime,&cfg.public,&rx,rho,&public_input,&mut tr);
    let logical_weights=cfg.private.column_weights(&mut runtime,&rx,rho);
    let mut ws=packed_weights(&mut runtime,logical_weights,k,physical_bits,&cfg0.map);
    runtime.release(&[logical_weights]);
    let h2:L=aggregate(n,|i|lag[i]*masks[i][1].sum());
    let lambda2=fields(&mut tr,&[h2]);assert_ne!(lambda2,L::ZERO,"general lambda2 excluded");
    let mut claim2=rho.iter().zip(endpoints).map(|(&a,b)|a*b).sum::<L>()+public_value+lambda2*h2;
    let omega=&cfg.omega;
    let mut indices=cfg0.map.clone();let mut sc2=vec![];let mut rp=vec![];
    for _ in 0..physical_bits {
        let (parents,pairs)=sparse_pairs(&indices);
        let zp=zs;let wp=ws;let mp=mask_shares;let pair=Arc::new(pairs);let prefix=rp.clone();let om=omega.to_vec();let ordinary_lag=lag.to_vec();let round_pair=pair.clone();
        let partials=runtime.run(move|w| {
            let v=sparse_round(&w.arrays[&wp.id],&w.arrays[&zp.id],&round_pair);
            let selector=Selector{polys:w.arrays[&mp.id].chunks_exact(3).map(|p|p.to_vec()).collect()};let q=selector.round(&prefix);
            (0..3).map(|u|om[w.rank]*v[u]+lambda2*ordinary_lag[w.rank]*q[u]).collect()
        });
        let partials=partials.into_iter().map(|p|p.try_into().unwrap()).collect::<Vec<[L;3]>>();
        let mut agg=[L::ZERO;3];for v in partials {for u in 0..3 {agg[u]+=v[u];}}
        assert_eq!(agg[0]+agg[1],claim2,"general SC2 columns");
        let r=fields(&mut tr,&agg);assert_ne!(r,L::ONE,"general SC2 excluded challenge");claim2=interp(&agg,r);sc2.push(agg);rp.push(r);
        runtime.run_effect(move|w| {
            let z=sparse_fold(&w.arrays[&zp.id],&pair,r);let weights=sparse_fold(&w.arrays[&wp.id],&pair,r);
            w.put(zp.id,z);w.put(wp.id,weights);vec![]
        });
        zs.len=n*parents.len();ws.len=n*parents.len();
        indices=parents;
    }
    // Only masked shares leave an owner. Never gather unmasked witness evaluations.
    let masked=runtime.run(move|w|vec![w.arrays[&zs.id][0]+w.arrays[&column_material.id][0]]);
    let column_conversion:Vec<L>=masked.into_iter().map(|v|v[0]).collect();
    let delta=ctx.open_packed_fft(&column_conversion);
    runtime.run_packets_effect(vec![bytes(&delta).to_vec();n],move|w,packet| {
        let delta:Vec<L>=packet.chunks_exact(32).map(bytemuck::pod_read_unaligned).collect();
        let ordinary=w.arrays[&column_material.id][1..].iter().zip(delta).map(|(&q,d)|q+d).collect();
        w.put(zs.id,ordinary);w.remove(column_material.id);vec![]
    });zs.len=n*k;
    tr.absorb(b"SC2 conversion",bytes(&column_conversion));
    let mut weights=ctx.open_packed_fft(&runtime.small(ws));
    let slot_weights=Vector{id:runtime.id(),len:n*k};
    runtime.run_packets_effect(vec![bytes(&weights).to_vec();n],move|w,packet|{w.put(slot_weights.id,packet.chunks_exact(32).map(bytemuck::pod_read_unaligned).collect());vec![]});
    for _ in 0..ctx.k.ilog2() as usize {
        let pairs:Vec<_>=(0..weights.len()/2).map(|j|[Some(2*j),Some(2*j+1)]).collect();
        let prefix=rp.clone();let ordinary_lag=lag.to_vec();let zp=zs;let mp=mask_shares;
        let partials=runtime.run(move|w| {
            let v=sparse_round(&w.arrays[&slot_weights.id],&w.arrays[&zp.id],&pairs);
            let selector=Selector{polys:w.arrays[&mp.id].chunks_exact(3).map(|p|p.to_vec()).collect()};let q=selector.round(&prefix);
            (0..3).map(|u|ordinary_lag[w.rank]*(v[u]+lambda2*q[u])).collect()
        });
        let mut agg=[L::ZERO;3];for v in partials {for u in 0..3 {agg[u]+=v[u];}}
        assert_eq!(agg[0]+agg[1],claim2,"general SC2 slots");
        let r=fields(&mut tr,&agg);assert_ne!(r,L::ONE,"general SC2 excluded challenge");claim2=interp(&agg,r);sc2.push(agg);rp.push(r);weights=fold_l(&weights,r);
        runtime.run_effect(move|w|{let next=fold_l(&w.arrays[&zp.id],r);let weight=fold_l(&w.arrays[&slot_weights.id],r);w.put(zp.id,next);w.put(slot_weights.id,weight);vec![]});zs.len/=2;
    }
    let ordinary_lag=lag.to_vec();let zp=zs;
    let value:L=runtime.run(move|w|vec![ordinary_lag[w.rank]*w.arrays[&zp.id][0]]).into_iter().map(|v|v[0]).sum();
    let y2=aggregate(n,|i|lag[i]*masks[i][1].value(&rp));
    assert_eq!(claim2,weights[0]*value+lambda2*y2);
    tr.absorb(b"private matrix endpoint",bytes(&[weights[0],value,y2]));
    let private=onehot::prove(&mut runtime,&cfg.private,index_prepared,&rx,&rp,rho,weights[0],&mut tr);
    let eta=fields(&mut tr,&[value,y2]);
    let mut gw=zk::selector_weights(&rx,3);gw.extend(zk::selector_weights(&rp,2).into_iter().map(|v|eta*v));
    let g=zk::open_g(&cfg0.g,&cfg0.gmap,&gw,gprepared,&mut tr);
    tr.absorb(b"G opening",&sha_zk::encode_pcs(&g));
    let inst=Instance{r_h:rp[..8].to_vec(),r_b:rp[8..physical_bits].to_vec(),r_a:rp[physical_bits..].to_vec(),s_x:value};
    tr.absorb(b"main instance",&inst.to_bytes());
    let (pcs,_,_)=protocol::open_prepared_in::<H>(&cfg0.pcs,&inst,prepared,&mut tr);
    runtime.flush();
    Proof{core:sha_zk::Proof{nonce,top,h1,h2,y1,y2,conversions,g,sc1,endpoints,sc2,value,pcs},
        column_conversion,matrix:MatrixProof{public_value,input,weight:weights[0],private}}
}

pub fn verify(vk:&VerifierKey,public:&[bool;2],proof:&Proof)->Result<(),String> {
    if !public[0] {return Err("public constant must be one".into());}
    let p=&proof.core;let total_sc2=vk.physical_bits+vk.slot_bits();
    if p.sc1.len()!=vk.row_bits||p.sc2.len()!=total_sc2||p.conversions.len()!=2||
        p.conversions.iter().any(|v|v.len()!=vk.n)||proof.column_conversion.len()!=vk.n {
        return Err("general proof shape".into());
    }
    let groot=p.g.roots.first().ok_or("missing G root")?;
    if p.pcs.roots.first()!=Some(&p.top) {return Err("witness root".into());}
    let hasher=Hasher::<H>::default();
    let mut tr=vk.transcript(&hasher,public,&p.nonce,&p.top,groot);
    let mut ch=tr.round(&ZERO,bytes(&[p.h1]));let lambda1=ch.field();
    if lambda1==L::ZERO {return Err("general lambda1 excluded".into());}
    let tau:Vec<L>=(0..vk.row_bits).map(|_|ch.field()).collect();
    let mut claim=lambda1*p.h1;let mut rx=vec![];
    let local_row_bits=vk.row_bits-vk.slot_bits();
    for (j,round) in p.sc1.iter().enumerate() {
        if j==local_row_bits {for x in &p.conversions {tr.absorb(b"SC1 conversion",bytes(x));}}
        if round[0]+round[1]!=claim {return Err(format!("general SC1 round {j}"));}
        let r=fields(&mut tr,round);if r==L::ONE {return Err("general SC1 excluded challenge".into());}claim=interp(round,r);rx.push(r);
    }
    if claim!=eq_eval(&tau,&rx)*(p.endpoints[0]*p.endpoints[1]+p.endpoints[2])+lambda1*p.y1 {
        return Err("general SC1 endpoint".into());
    }
    let mut ep=p.endpoints.to_vec();ep.push(p.y1);
    let mut ch=tr.round(&ZERO,bytes(&ep));let rho=std::array::from_fn(|_|ch.field());
    let input=public.map(bool_field);
    public_input::verify(&vk.public,&rx,rho,&input,proof.matrix.public_value,&proof.matrix.input,&mut tr)?;
    let lambda2=fields(&mut tr,&[p.h2]);if lambda2==L::ZERO {return Err("general lambda2 excluded".into());}
    let mut claim2=rho.iter().zip(p.endpoints).map(|(&a,b)|a*b).sum::<L>()+proof.matrix.public_value+lambda2*p.h2;
    let mut rp=vec![];
    for (j,round) in p.sc2.iter().enumerate() {
        if j==vk.physical_bits {tr.absorb(b"SC2 conversion",bytes(&proof.column_conversion));}
        if round[0]+round[1]!=claim2 {return Err(format!("general SC2 round {j}"));}
        let r=fields(&mut tr,round);if r==L::ONE {return Err("general SC2 excluded challenge".into());}claim2=interp(round,r);rp.push(r);
    }
    if claim2!=proof.matrix.weight*p.value+lambda2*p.y2 {return Err("general SC2 endpoint".into());}
    tr.absorb(b"private matrix endpoint",bytes(&[proof.matrix.weight,p.value,p.y2]));
    onehot::verify(&vk.private,&rx,&rp,rho,proof.matrix.weight,&proof.matrix.private,&mut tr)?;
    let eta=fields(&mut tr,&[p.value,p.y2]);
    let mut gw=zk::selector_weights(&rx,3);gw.extend(zk::selector_weights(&rp,2).into_iter().map(|v|eta*v));
    zk::verify_g(&vk.g,&vk.gmap,&gw,p.y1+eta*p.y2,&p.g,&mut tr)?;
    tr.absorb(b"G opening",&sha_zk::encode_pcs(&p.g));
    let inst=Instance{r_h:rp[..8].to_vec(),r_b:rp[8..vk.physical_bits].to_vec(),r_a:rp[vk.physical_bits..].to_vec(),s_x:p.value};
    tr.absorb(b"main instance",&inst.to_bytes());
    protocol::verify_in::<H>(&vk.pcs,&inst,&p.pcs,&mut tr,zk::BIT_ROLE).map(|_|())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{SeedableRng,rngs::StdRng};
    #[test]fn compact_proof_is_deterministic_and_versioned() {
        let c=Circuit::generate_task(64,42,16,super::super::Task::NandCopy).unwrap();
        let mut rng=StdRng::seed_from_u64(718);let(w,public)=c.witness(&mut rng);
        let cfg=Config::new(&c,16,16,3).unwrap();let p=prove(&cfg,&c,&w,&public,&mut rng);
        let encoded=super::super::codec::encode_proof(&p);
        assert_eq!(&encoded[..8],b"GENPRF05");
        let vk=cfg.verifier_key();verify(&vk,&public,&p).unwrap();
        let mut rng=StdRng::seed_from_u64(718);let(w2,public2)=c.witness(&mut rng);
        let p2=prove(&cfg,&c,&w2,&public2,&mut rng);
        assert_eq!(encoded,super::super::codec::encode_proof(&p2));
        for magic in [b"GENPRF01",b"GENPRF03",b"GENPRF04"] {let mut old=encoded.clone();old[..8].copy_from_slice(magic);
            assert!(super::super::codec::decode_proof(&vk,&old).is_err());}
        let mut old_key=super::super::codec::encode_key(&vk);old_key[..8].copy_from_slice(b"GENKEY03");
        assert!(super::super::codec::decode_key(&old_key).is_err());
        let mut wrong_key=cfg.verifier_key();wrong_key.public.log+=1;
        assert!(super::super::codec::decode_key(&super::super::codec::encode_key(&wrong_key)).is_err());
    }
    #[test]
    fn gamma520_regenerates_layout_and_all_query_bindings() {
        let c=Circuit::generate_task(16,42,16,super::super::Task::NandCopy).unwrap();
        let new=Config::new(&c,8,520,4).unwrap();let old=Config::new(&c,8,871,4).unwrap();
        assert_eq!(crate::params::ceil_log2(520+2),crate::params::ceil_log2(871+2));
        assert_ne!(new.geometry.pcs.layout.pad,old.geometry.pcs.layout.pad);
        assert_ne!(new.binding,old.binding);
        for p in [&new.geometry.pcs.params,&new.geometry.g.params]{assert_eq!(p.gamma,520);assert_eq!(p.tau,4);assert_eq!(p.beta,2);assert_eq!(p.salt_bytes,32);}
        assert_eq!(new.private.key.params.gamma,520);assert_eq!(new.public.key.queries,520);
        let mut rng=StdRng::seed_from_u64(520);let(w,public)=c.witness(&mut rng);
        let p=prove(&new,&c,&w,&public,&mut rng);let vk=new.verifier_key();verify(&vk,&public,&p).unwrap();
        assert_eq!(p.matrix.private.opening.openings.len(),520);assert_eq!(p.matrix.input.opening.openings.len(),520);
        let encoded=super::super::codec::encode_proof(&p);let decoded=super::super::codec::decode_proof(&vk,&encoded).unwrap();verify(&vk,&public,&decoded).unwrap();
        assert!(verify(&old.verifier_key(),&public,&p).is_err());
        assert!(super::super::codec::decode_proof(&old.verifier_key(),&encoded).is_err());
    }
    #[test]
    fn nand_full_formal_parameters_and_authenticated_mutation() {
        let c=Circuit::generate_task(16,42,16,super::super::Task::NandCopy).unwrap();
        let mut rng=StdRng::seed_from_u64(819);let(w,public)=c.witness(&mut rng);
        let cfg=Config::new(&c,8,871,4).unwrap();let vk=cfg.verifier_key();
        let mut proof=prove(&cfg,&c,&w,&public,&mut rng);verify(&vk,&public,&proof).unwrap();
        assert_eq!(cfg.parameter_record()["public_columns"]["batch_size"],6);
        let encoded=super::super::codec::encode_proof(&proof);let decoded=super::super::codec::decode_proof(&vk,&encoded).unwrap();verify(&vk,&public,&decoded).unwrap();
        proof.matrix.private.opening.openings[0][0].values[0]+=L::ONE;
        assert!(verify(&vk,&public,&proof).is_err());
    }
    #[test]
    fn general_cross_slot_full_proof_and_mutations() {
        let c=Circuit::generate(64,42,16).unwrap();
        let mut rng=StdRng::seed_from_u64(718);
        let (w,public)=c.witness(&mut rng);
        for (n,b) in [(8,3),(16,5)] {
            let started=Instant::now();let cfg=Config::new_block(&c,n,16,3,b).unwrap();
            assert!(c.cross_slot_entries(n).unwrap()>0);
            let mut p=prove(&cfg,&c,&w,&public,&mut rng);let vk=cfg.verifier_key();
            verify(&vk,&public,&p).unwrap();
            let decoded_key=super::super::codec::decode_key(&super::super::codec::encode_key(&vk)).unwrap();
            let encoded=super::super::codec::encode_proof(&p);
            let decoded=super::super::codec::decode_proof(&decoded_key,&encoded).unwrap();
            verify(&decoded_key,&public,&decoded).unwrap();
            assert!(super::super::codec::decode_proof(&vk,&encoded[..encoded.len()-1]).is_err());
            let mut trailing=encoded.clone();trailing.push(0);
            assert!(super::super::codec::decode_proof(&vk,&trailing).is_err());
            let stats=cfg.actor_stats();
            assert!(stats.iter().all(|s|s.resident_array_peak_cells>0));
            assert_eq!(stats.iter().map(|s|s.sent_bytes).sum::<u64>(),stats.iter().map(|s|s.received_bytes).sum::<u64>());
            // Reusing the setup retires old online arrays and uses fresh ideal randomness.
            if n==8 {
                let second=prove(&cfg,&c,&w,&public,&mut rng);verify(&vk,&public,&second).unwrap();
                let next_stats=cfg.actor_stats();
                assert_eq!(stats.iter().map(|s|s.resident_array_peak_cells).collect::<Vec<_>>(),next_stats.iter().map(|s|s.resident_array_peak_cells).collect::<Vec<_>>());
            }
            for (message,forced,expected) in [(bytes(&[p.core.h1]),L::ZERO,"general lambda1 excluded"),
                (bytes(&[p.core.h2]),L::ZERO,"general lambda2 excluded"),
                (bytes(&p.core.sc1[0]),L::ONE,"general SC1 excluded challenge"),
                (bytes(&p.core.sc2[0]),L::ONE,"general SC2 excluded challenge"),
                (bytes(&[p.matrix.input.opening.rounds[0].0,p.matrix.input.opening.rounds[0].1]),L::ONE,"public excluded challenge")] {
                let result=crate::fs::testing::with_field(message,forced,||verify(&vk,&public,&p));
                assert_eq!(result.unwrap_err(),expected);
            }
            p.column_conversion[0]+=L::ONE;assert!(verify(&vk,&public,&p).is_err());p.column_conversion[0]+=L::ONE;
            p.matrix.input.values[0]+=L::ONE;assert!(verify(&vk,&public,&p).is_err());p.matrix.input.values[0]+=L::ONE;
            let mut wrong=public;wrong[1]=!wrong[1];assert!(verify(&vk,&wrong,&p).is_err());
            p.core.sc2[0][0]+=L::ONE;assert!(verify(&vk,&public,&p).is_err());
            eprintln!("general complete N={n}: {:?}",started.elapsed());
        }
    }
}
