//! General field-valued linear openings over the existing padded Fold backend.
//! No owner plaintext is needed when committing already-shared online oracle rows.
use crate::{field::{Field,L,Random,chi},fs::Transcript,merkle::{Hash,Hasher,Tree},protocol::{self,Party,Prepared,Proof,TAG_TAIL},setup::Setup};
use binius_hash::Blake3HashSuite as H;
use rand::{Rng,RngExt,SeedableRng,rngs::StdRng};
use std::{collections::HashSet,time::{Duration,Instant}};

/// Sequential logical-worker spans and actual message lengths for this adapter.
#[derive(Debug)]
pub struct Stage {pub command:u8,pub party_ns:Vec<u64>,pub request_bytes:Vec<usize>,pub response_bytes:Vec<usize>}
thread_local!{static TRACE:std::cell::RefCell<Option<Vec<Stage>>>=const{std::cell::RefCell::new(None)};}
pub fn trace_start(){TRACE.with(|t|{assert!(t.borrow().is_none());*t.borrow_mut()=Some(vec![]);});}
pub fn trace_take()->Vec<Stage>{TRACE.with(|t|t.borrow_mut().as_mut().map(std::mem::take).unwrap_or_default())}
pub fn trace_stop()->Vec<Stage>{TRACE.with(|t|t.borrow_mut().take().unwrap_or_default())}
fn record(stage:Stage){TRACE.with(|t|if let Some(trace)=t.borrow_mut().as_mut(){trace.push(stage);});}
fn measured<R:Send>(parties:&mut[Party],tag:u8,down:usize,up:usize,f:impl Fn(usize,&mut Party)->R+Sync+Send)->Vec<R>{
    let n=parties.len();let result=crate::parallel::parties(parties,|i,q|{let t=Instant::now();let value=f(i,q);(value,t.elapsed().as_nanos()as u64)});
    let(values,times):(Vec<_>,Vec<_>)=result.into_iter().unzip();record(Stage{command:tag,party_ns:times,request_bytes:vec![if down==0{0}else{13+down};n],response_bytes:vec![if up==0{0}else{13+up};n]});values
}

/// Separate format from PCS002: field functionals have no binary frontend t-vector.
pub fn encode_proof(proof:&Proof)->Vec<u8>{
 let inner=crate::sha_zk::encode_pcs(proof);let mut out=b"B2FLD001".to_vec();out.extend((inner.len()as u64).to_le_bytes());out.extend(inner);out
}
pub fn decode_proof(setup:&Setup,bytes:&[u8])->Result<Proof,String>{
 let mut reader=crate::sha_zk::Reader(bytes);if reader.take(8)?!=b"B2FLD001"{return Err("field PCS format".into());}
 let proof=reader.pcs(setup,false)?;if !reader.0.is_empty(){return Err("field PCS trailing bytes".into());}Ok(proof)
}

/// Fresh ideal preprocessing for masked aggregation, consumed by exactly one opening.
/// Individual TCP records carry masked contributions; only their sum is disclosed.
pub struct Aggregation { masks:Vec<Vec<L>> }
pub fn prepare_aggregation(setup:&Setup,rng:&mut impl Rng)->Aggregation{
 let n=setup.params.n_parties;let count=1+2*setup.params.folds();
 let mut masks=vec![vec![L::ZERO;count];n];
 for j in 0..count{let mut sum=L::ZERO;for row in &mut masks[..n-1]{row[j]=L::random(&mut *rng);sum+=row[j];}masks[n-1][j]=-sum;}
 Aggregation{masks}
}

fn validate(setup:&Setup,map:&[(usize,usize)],weights:&[L])->Result<(),String>{
 if map.is_empty()||map.len()!=weights.len(){return Err("field PCS map/weight shape".into());}
 let mut seen=HashSet::new();
 for &(y,x) in map {if y>=setup.params.k()||x>=setup.params.n()||setup.layout.pad.binary_search(&x).is_ok()||!seen.insert((y,x)){return Err("field PCS address".into());}}
 Ok(())
}
fn bind(setup:&Setup,map:&[(usize,usize)],weights:&[L],value:L,root:Hash,role:u64,tr:&mut Transcript<'_,H>){
 let p=&setup.params;
 let mut binding=Vec::new();
 for n in [p.n_parties,p.ell,p.beta,p.gamma,p.tau,p.salt_bytes,map.len()]{binding.extend((n as u64).to_le_bytes());}
 binding.extend(role.to_le_bytes());binding.extend(root);
 for &(y,x) in map{binding.extend((y as u64).to_le_bytes());binding.extend((x as u64).to_le_bytes());}
 binding.extend(bytemuck::cast_slice(weights));binding.extend(bytemuck::bytes_of(&value));
 tr.absorb(b"field PCS functional v1",&binding);
}

/// Rows must already contain low-degree shares and independent preprocessed padding.
/// Sharing/conversion is the caller's protocol. Encoding and hashing happen here online.
/// The returned state is consumed by one opening, preventing accidental opening-mask reuse.
pub fn commit_rows(setup:&Setup,rows:Vec<Vec<L>>,role:u64,rng:&mut impl Rng)->Result<Prepared,String>{
 let p=&setup.params;
 if !(1..=255).contains(&role){return Err("field PCS role must fit low byte".into());}
 if rows.len()!=p.n_parties||rows.iter().any(|r|r.len()!=p.n()){return Err("field PCS share-row shape".into());}
 let mut parties:Vec<_>=rows.into_iter().enumerate().map(|(i,row)|{let mut q=Party::new(i,p.n(),0);q.row=row;q.rng=StdRng::from_seed(rng.random());q}).collect();
 measured(&mut parties,180,1,32,|_,q|{let t=Instant::now();let cw=setup.row.encode(&q.row);q.time.encode+=t.elapsed();q.commit_layer(setup,&Hasher::<H>::scoped(role),0,cw);});
 let root=Tree::build(&Hasher::<H>::scoped(role).at_layer(0),crate::transport::hashes(parties.iter().map(|q|q.subtrees[0].root()).collect())).root();
 Ok(Prepared{root,parties,role,preprocessing:Duration::ZERO,client_share:Duration::ZERO})
}

pub fn open(
    setup: &Setup,
    map: &[(usize,usize)],
    weights: &[L],
    value: L,
    prepared: Prepared,
    aggregation: Aggregation,
    tr: &mut Transcript<'_, H>,
) -> Result<Proof,String> {
    validate(setup,map,weights)?;
    if aggregation.masks.len()!=setup.params.n_parties||aggregation.masks.iter().any(|m|m.len()!=1+2*setup.params.folds()){return Err("field PCS aggregation shape".into());}
    let role=prepared.role;
    if !(1..=255).contains(&role){return Err("field PCS role must fit low byte".into());}
    bind(setup,map,weights,value,prepared.root,role,tr);
    let p = &setup.params;
    let hasher = Hasher::<H>::scoped(role);
    let mut parties = prepared.parties;
    let mut roots = vec![prepared.root];
    let zero = [0; 32];
    let mut c = tr.round(&prepared.root, b"v04 G functional");
    let omega: Vec<L> = (0..setup.n_omega()).map(|_| c.field()).collect();
    let mw = setup.mask_weight(&omega);
    let h_omega: L = crate::transport::scalars(measured(&mut parties,181,32*omega.len(),32,|_,q| q.h_omega(setup,&mw)+aggregation.masks[q.id][0])).into_iter().sum();
    let eps = tr.round(&zero, bytemuck::cast_slice(&[h_omega])).field();
    assert_ne!(eps, L::ZERO);
    assert!(!omega.contains(&L::ZERO));
    measured(&mut parties,182,32*(weights.len()+1),0,|_,q| {
        q.weight = vec![L::ZERO; p.n()];
        let l = setup.lagrange[q.id][0];
        for (&(y,x), &w) in map.iter().zip(weights) {
            q.weight[x] += setup.lagrange[q.id][y] * w;
        }
        for &(x, w) in &mw {
            q.weight[x] += l * eps * w;
        }
    });
    let mut coeffs = Vec::new();
    for j in 0..p.folds() {
        let (mut a, mut b) = (L::ZERO, L::ZERO);
        let partials=measured(&mut parties,183,0,64,|_,q| {let(a,b)=q.round_poly();(a+aggregation.masks[q.id][1+2*j],b+aggregation.masks[q.id][2+2*j])});
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
        measured(&mut parties,184,32,if j+1<p.folds(){32}else{0},|_,q| q.fold(setup,&Hasher::<H>::scoped(role),j,r));
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
    let mut tail_times=Vec::new();
    for q in &mut parties {
        let start=Instant::now();
        let mut salt = [0; 32];
        q.rng.fill_bytes(&mut salt);
        leaves.push(hasher.at_layer(TAG_TAIL).leaf(
            TAG_TAIL,
            q.id as u64,
            bytemuck::cast_slice(&q.row),
            &salt,
        ));
        tail_salts.push(salt);tail_times.push(start.elapsed().as_nanos()as u64);
    }
    record(Stage{command:185,party_ns:tail_times,request_bytes:vec![0;p.n_parties],response_bytes:vec![45;p.n_parties]});
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
    let mut query_times=vec![0u64;p.n_parties];let mut query_bytes=vec![0usize;p.n_parties];
    let openings = queries
        .iter()
        .map(|&(i, q)| {
            (0..p.folds())
                .map(|j| {
                    let start=Instant::now();
                    let x = q >> j;
                    let party = &parties[i];
                    let path = party.subtrees[j].path(x);
                    let opening=protocol::Opening {
                        values: [party.codewords[j][2 * x], party.codewords[j][2 * x + 1]],
                        salt: party.salts[j][x],
                        path,
                    };query_bytes[i]+=96+32*opening.path.len();query_times[i]+=start.elapsed().as_nanos()as u64;opening
                })
                .collect()
        })
        .collect();
    record(Stage{command:186,party_ns:query_times,request_bytes:vec![13+16*queries.len();p.n_parties],response_bytes:query_bytes.into_iter().map(|b|if b==0{0}else{13+b}).collect()});
    let mut openings=crate::transport::openings(openings,&queries,p.n_parties);
    // Workers own their subtree paths. The coordinator appends its top-tree path.
    for(ops,&(i,_))in openings.iter_mut().zip(&queries){for(j,op)in ops.iter_mut().enumerate(){op.path.extend(tops[j].path(i));}}
    record(Stage{command:187,party_ns:vec![0;p.n_parties],request_bytes:vec![0;p.n_parties],response_bytes:vec![13+32*(1<<p.tau)+32;p.n_parties]});
    let tails=crate::transport::values(parties.iter().map(|q|q.row.clone()).collect(),true);
    let tail_salts=crate::transport::hashes(tail_salts);
    Ok(Proof {
        roots,
        tail_root,
        xi: L::ZERO,
        t: vec![],
        h_omega,
        coeffs,
        tails,
        tail_salts,
        openings,
    })
}

pub fn verify(
    setup: &Setup,
    map: &[(usize,usize)],
    weights: &[L],
    value: L,
    root: Hash,
    role: u64,
    proof: &Proof,
    tr: &mut Transcript<'_, H>,
) -> Result<(), String> {
    validate(setup,map,weights)?;
    if !(1..=255).contains(&role){return Err("field PCS role must fit low byte".into());}
    if proof.roots.first()!=Some(&root) { return Err("field PCS initial root".into()); }
    bind(setup,map,weights,value,root,role,tr);
    let p = &setup.params;
    let hasher = Hasher::<H>::scoped(role);
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
    for (&(y,x), &w) in map.iter().zip(weights) {
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
 use crate::{field::{Field,L,Random},params::Params,setup::{Setup,Witness},protocol,merkle::Hasher,fs::Transcript};
 use binius_hash::Blake3HashSuite as H;
 use rand::{SeedableRng,rngs::StdRng};
 #[test]
 fn all_slot_linear_opening_and_binding_mutations() {
  let mut rng=StdRng::seed_from_u64(57);
  let setup=Setup::new(Params{n_parties:8,ell:12,beta:2,gamma:16,tau:3,salt_bytes:32});
  let map:Vec<_>=setup.layout.owned.iter().flatten().take(9).flat_map(|&x|(0..setup.params.k()).map(move|y|(y,x))).collect();
  let mut wit=Witness{table:vec![L::ZERO;setup.params.k()*setup.params.n()]};
  for &(y,x) in &map {wit.table[y*setup.params.n()+x]=L::random(&mut rng);}
  let weights:Vec<_>=map.iter().map(|_|L::random(&mut rng)).collect();
  let value=map.iter().zip(&weights).map(|(&(y,x),&w)|wit.table[y*setup.params.n()+x]*w).sum();
  let prepared=protocol::prepare_random::<H>(&setup,&wit,&mut rng,73);
  let rows=prepared.parties.into_iter().map(|q|q.row).collect();
  let prepared=commit_rows(&setup,rows,73,&mut rng).unwrap();
  let root=prepared.root;
  let h=Hasher::<H>::default();
  let masks=prepare_aggregation(&setup,&mut rng);
  let proof=open(&setup,&map,&weights,value,prepared,masks,&mut Transcript::new_global(&h,b"field-test")).unwrap();
  let encoded=encode_proof(&proof);let proof=decode_proof(&setup,&encoded).unwrap();
  assert!(decode_proof(&setup,&encoded[..encoded.len()-1]).is_err());let mut trailing=encoded.clone();trailing.push(0);assert!(decode_proof(&setup,&trailing).is_err());
  let verify=|map:&[(usize,usize)],weights:&[L],value:L,root,role,proof:&protocol::Proof|super::verify(&setup,map,weights,value,root,role,proof,&mut Transcript::new_global(&h,b"field-test"));
  assert!(verify(&map,&weights,value,root,73,&proof).is_ok());
  assert!(verify(&map,&weights,value+L::ONE,root,73,&proof).is_err());
  let mut bad=proof.clone();bad.openings[0][0].values[0]+=L::ONE;
  assert!(verify(&map,&weights,value,root,73,&bad).is_err());
  let mut badroot=root;badroot[0]^=1;
  assert!(verify(&map,&weights,value,badroot,73,&proof).is_err());
  assert!(verify(&map,&weights,value,root,74,&proof).is_err());
  assert!(verify(&map,&weights,value,root,256,&proof).is_err());
  let mut badmap=map.clone();badmap[0].0=1;
  assert!(verify(&badmap,&weights,value,root,73,&proof).is_err());
  assert!(verify(&map,&weights[..weights.len()-1],value,root,73,&proof).is_err());
  let mut badweights=weights;badweights[0]+=L::ONE;
  assert!(verify(&map,&badweights,value,root,73,&proof).is_err());
 }
 #[test]
 fn aggregation_masks_preserve_sum_and_corrupt_view(){
  let mut rng=StdRng::seed_from_u64(59);
  let setup=Setup::new(Params{n_parties:8,ell:12,beta:2,gamma:16,tau:3,salt_bytes:32});
  let masks=prepare_aggregation(&setup,&mut rng);let n=setup.params.n_parties;let t=n/4;
  for j in 0..1+2*setup.params.folds(){
   let values:Vec<_>=(0..n).map(|_|L::random(&mut rng)).collect();
   let mut delta=vec![L::ZERO;n];for d in &mut delta[t..n-1]{*d=L::random(&mut rng);}delta[n-1]=-delta.iter().copied().sum::<L>();
   let changed_masks:Vec<_>=(0..n).map(|i|masks.masks[i][j]-delta[i]).collect();
   assert_eq!(changed_masks.iter().copied().sum::<L>(),L::ZERO);
   for i in 0..n{assert_eq!(values[i]+masks.masks[i][j],values[i]+delta[i]+changed_masks[i]);if i<t{assert_eq!(changed_masks[i],masks.masks[i][j]);}}
   assert_eq!((0..n).map(|i|values[i]+masks.masks[i][j]).sum::<L>(),values.iter().copied().sum());
  }
 }
}
