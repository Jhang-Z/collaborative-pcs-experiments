//! Pappas/Spartan read-only memory sparse evaluation, adapted to characteristic two.
//! Authenticated read/write timestamps are encoded separately (never field t+1).
use crate::{field::{Field,L,from_words,basis,chi,eq_expand},fs::Transcript,
 public_pcs::{self,Committed},product_tree::{self,Tree},code::fold_coeffs,spartan::{omega,interp,eq_eval},field::from_b};
use binius_hash::Blake3HashSuite as H;
use std::collections::BTreeSet;
const ZERO:[u8;32]=[0;32];
fn bytes(x:&[L])->&[u8]{bytemuck::cast_slice(x)}
fn label(i:usize)->L{from_words([i as u128,0])}
#[derive(Clone,Debug)]
pub struct Key {pub row_bits:usize,pub col_bits:usize,pub entry_bits:usize,pub channel_bits:usize,pub pcs:public_pcs::Key,pub final_pcs:public_pcs::Key}
impl Key {
 pub fn channels(&self)->usize{15}
 pub fn chunks(&self)->[usize;4]{[self.row_bits/2,self.row_bits-self.row_bits/2,self.col_bits/2,self.col_bits-self.col_bits/2]}
 pub fn table_bits(&self)->usize{*self.chunks().iter().max().unwrap().max(&2)}
 pub fn binding(&self)->Vec<u8>{let mut b=self.pcs.binding();for n in [self.row_bits,self.col_bits,self.entry_bits,self.channel_bits]{b.extend((n as u64).to_le_bytes());}b.extend(self.final_pcs.binding());b}
 pub fn valid(&self)->bool{self.row_bits<usize::BITS as usize&&self.col_bits<usize::BITS as usize&&self.entry_bits>=2&&self.entry_bits<usize::BITS as usize-4&&self.channel_bits==4&&self.entry_bits+4==self.pcs.log&&self.final_pcs.log==self.table_bits()+2&&self.pcs.queries==self.final_pcs.queries&&self.pcs.queries>0}
}
pub struct Index {pub key:Key,pub entries:Vec<(usize,usize,usize)>,pub committed:Committed,pub final_committed:Committed,addresses:[Vec<usize>;4]}
#[derive(Clone)]
pub struct Proof {
 pub auxiliary:public_pcs::Key,pub rounds:Vec<Vec<L>>,pub endpoints:Vec<L>,
 pub reads:product_tree::Proof,pub table:product_tree::Proof,pub memory_endpoints:Vec<L>,pub final_endpoints:[L;4],
 pub opening:public_pcs::Proof,pub auxiliary_opening:public_pcs::Proof,pub final_opening:public_pcs::Proof,
}
impl Proof {pub fn encode(&self)->Vec<u8>{let mut b=self.auxiliary.binding();b.extend((self.rounds.len() as u64).to_le_bytes());for q in &self.rounds{b.extend(bytes(q));}b.extend(bytes(&self.endpoints));b.extend(self.reads.encode());b.extend(self.table.encode());b.extend(bytes(&self.memory_endpoints));b.extend(bytes(&self.final_endpoints));b.extend(self.opening.encode());b.extend(self.auxiliary_opening.encode());b.extend(self.final_opening.encode());b}}
pub fn index(row_bits:usize,col_bits:usize,entries:Vec<(usize,usize,usize)>,queries:usize)->Index{
 assert!(row_bits<usize::BITS as usize&&col_bits<usize::BITS as usize);
 let mut set=BTreeSet::new();for e in entries{assert!(e.0<3&&e.1<1<<row_bits&&e.2<1<<col_bits);if !set.insert(e){set.remove(&e);}}
 let entries:Vec<_>=set.into_iter().collect();let count=entries.len().max(4).next_power_of_two();let chunks=[row_bits/2,row_bits-row_bits/2,col_bits/2,col_bits-col_bits/2];let table_bits=(*chunks.iter().max().unwrap()).max(2);let b=1<<table_bits;
 let mut values=vec![L::ZERO;16*count];let mut finals=vec![L::ZERO;4*b];let mut addresses:[Vec<usize>;4]=std::array::from_fn(|_|vec![0;count]);
 for(i,&(t,row,col))in entries.iter().enumerate(){addresses[0][i]=row&((1<<chunks[0])-1);addresses[1][i]=row>>chunks[0];addresses[2][i]=col&((1<<chunks[2])-1);addresses[3][i]=col>>chunks[2];values[(12+t)*count+i]=L::ONE;}
 for c in 0..4 {let mut counters=vec![0usize;b];for i in 0..count{let a=addresses[c][i];values[c*count+i]=label(a);values[(4+c)*count+i]=label(counters[a]);counters[a]+=1;values[(8+c)*count+i]=label(counters[a]);}for i in 0..b{finals[c*b+i]=label(counters[i]);}}
 let committed=public_pcs::commit(values,queries);let final_committed=public_pcs::commit(finals,queries);let key=Key{row_bits,col_bits,entry_bits:count.trailing_zeros() as usize,channel_bits:4,pcs:committed.key.clone(),final_pcs:final_committed.key.clone()};Index{key,entries,committed,final_committed,addresses}
}
impl Index {
 pub fn evaluate(&self,row:&[L],col:&[L],rho:[L;3])->L{self.entries.iter().map(|&(t,i,j)|rho[t]*chi(i,row)*chi(j,col)).sum()}
 pub fn column_weights(&self,row:&[L],rho:[L;3])->Vec<L>{let mut w=vec![L::ZERO;1<<self.key.col_bits];for &(t,i,j) in &self.entries{w[j]+=rho[t]*chi(i,row);}w}
}
fn begin(key:&Key,row:&[L],col:&[L],rho:[L;3],value:L,tr:&mut Transcript<'_,H>){tr.absorb(b"memory sparse index v2",&key.binding());tr.absorb(b"sparse row",bytes(row));tr.absorb(b"sparse column",bytes(col));tr.absorb(b"sparse mix/value",bytes(&[rho[0],rho[1],rho[2],value]));}
fn split<'a>(k:&Key,row:&'a[L],col:&'a[L])->[&'a[L];4]{[&row[..k.row_bits/2],&row[k.row_bits/2..],&col[..k.col_bits/2],&col[k.col_bits/2..]]}
fn endpoints(idx:&Index,aux:&Committed,r:&[L])->Vec<L>{let n=1<<idx.key.entry_bits;crate::parallel::map(19,|j|if j<15{public_pcs::evaluate(&idx.committed.values[j*n..(j+1)*n],r)}else{public_pcs::evaluate(&aux.values[(j-15)*n..(j-14)*n],r)})}
// Bind all endpoint values before sampling their channel-combination points.
fn claims(r:&[L],e:&[L],tr:&mut Transcript<'_,H>)->((Vec<L>,L),(Vec<L>,L)){
 let mut ch=tr.round(&ZERO,bytes(e));let ri:Vec<_>=(0..4).map(|_|ch.field()).collect();let ra:Vec<_>=(0..2).map(|_|ch.field()).collect();
 let vi=e[..15].iter().enumerate().map(|(i,&v)|chi(i,&ri)*v).sum();let va=e[15..].iter().enumerate().map(|(i,&v)|chi(i,&ra)*v).sum();let mut pi=r.to_vec();pi.extend(ri);let mut pa=r.to_vec();pa.extend(ra);((pi,vi),(pa,va))
}
fn read_leaf(e:&[L],r:&[L],hash:[L;3])->L{(0..4).map(|c|chi(c,&r[1..])*(L::ONE+hash[0]*e[15+c]+hash[1]*(e[4+c]+r[0]*(e[4+c]+e[8+c]))+hash[2]*e[c])).sum()}
fn table_leaf(k:&Key,queries:[&[L];4],e:&[L;4],r:&[L],hash:[L;3])->L{let n=k.table_bits();let addr:L=r[..n].iter().enumerate().map(|(j,&x)|basis(j)*x).sum();(0..4).map(|c|{let q=queries[c];let v=eq_eval(q,&r[..q.len()])*r[q.len()..n].iter().map(|&x|L::ONE+x).product::<L>();chi(c,&r[n+1..])*(L::ONE+hash[0]*v+hash[1]*r[n]*e[c]+hash[2]*addr)}).sum()}
fn bind_products(reads:&[L;8],table:&[L;8],tr:&mut Transcript<'_,H>)->Result<(),String>{for c in 0..4{if reads[2*c]*table[2*c+1]!=reads[2*c+1]*table[2*c]{return Err("memory multiset products".into());}}tr.absorb(b"memory products",bytes(&[reads.as_slice(),table.as_slice()].concat()));Ok(())}
fn final_claim(r:&[L],e:&[L;4],tr:&mut Transcript<'_,H>)->(Vec<L>,L){let mut ch=tr.round(&ZERO,bytes(e));let rc:Vec<_>=(0..2).map(|_|ch.field()).collect();let value=public_pcs::evaluate(e,&rc);let mut p=r.to_vec();p.extend(rc);(p,value)}
pub fn prove(idx:&Index,row:&[L],col:&[L],rho:[L;3],value:L,tr:&mut Transcript<'_,H>)->Proof{
 let clock=std::time::Instant::now();let k=&idx.key;assert_eq!((row.len(),col.len()),(k.row_bits,k.col_bits));begin(k,row,col,rho,value,tr);let count=1<<k.entry_bits;let queries=split(k,row,col);
 let tables:[Vec<L>;4]=queries.map(eq_expand);
 let aux_values=crate::parallel::map(4*count,|i|tables[i/count][idx.addresses[i/count][i%count]]);let aux=public_pcs::commit(aux_values,k.pcs.queries);tr.absorb(b"memory read values",&aux.key.binding());let aux_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();
 let mut f:Vec<Vec<L>>=(0..4).map(|c|aux.values[c*count..(c+1)*count].to_vec()).collect();f.push(crate::parallel::map(count,|i|(0..3).map(|t|rho[t]*idx.committed.values[(12+t)*count+i]).sum()));
 let(mut rounds,mut r,mut claim)=(vec![],vec![],value);
 for _ in 0..k.entry_bits{let q=product_tree::round(&f);assert_eq!(q[0]+q[1],claim);let x=tr.round(&ZERO,bytes(&q)).field();claim=product_tree::interpolate(&q,x);r.push(x);rounds.push(q);crate::parallel::map_mut(&mut f,|_,v|{*v=fold_coeffs(v,x);});}
 let end=endpoints(idx,&aux,&r);assert_eq!(claim,(0..4).map(|c|end[15+c]).product::<L>()*(0..3).map(|t|rho[t]*end[12+t]).sum::<L>());let(ic1,ac1)=claims(&r,&end,tr);let main_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();
 let mut ch=tr.round(&ZERO,b"memory tuple compression");let hash:[L;3]=std::array::from_fn(|_|ch.field());
 let reads=Tree::new(crate::parallel::map(8*count,|i|{let(c,j)=((i/count)/2,i%count);let time=(if i/count%2==0{4}else{8})+c;L::ONE+hash[0]*aux.values[c*count+j]+hash[1]*idx.committed.values[time*count+j]+hash[2]*idx.committed.values[c*count+j]}),k.entry_bits);
 let b=1<<k.table_bits();let table=Tree::new(crate::parallel::map(8*b,|i|{let(c,j)=((i/b)/2,i%b);L::ONE+hash[0]*tables[c].get(j).copied().unwrap_or(L::ZERO)+hash[2]*label(j)+if i/b%2==1{hash[1]*idx.final_committed.values[c*b+j]}else{L::ZERO}}),k.table_bits());
 let tree_build_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();bind_products(&reads.roots,&table.roots,tr).unwrap();let(reads,rr,rv)=product_tree::prove(reads,tr);let memory_endpoints=endpoints(idx,&aux,&rr[..k.entry_bits]);assert_eq!(rv,read_leaf(&memory_endpoints,&rr[k.entry_bits..],hash));let(ic2,ac2)=claims(&rr[..k.entry_bits],&memory_endpoints,tr);
 let(table,rt,tv)=product_tree::prove(table,tr);let final_endpoints=std::array::from_fn(|c|public_pcs::evaluate(&idx.final_committed.values[c*b..(c+1)*b],&rt[..k.table_bits()]));assert_eq!(tv,table_leaf(k,queries,&final_endpoints,&rt,hash));let(fc,fv)=final_claim(&rt[..k.table_bits()],&final_endpoints,tr);let tree_prove_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();
 let opening=public_pcs::open_batch(&idx.committed,&[ic1.0,ic2.0],&[ic1.1,ic2.1],tr);let index_open_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();let auxiliary_opening=public_pcs::open_batch(&aux,&[ac1.0,ac2.0],&[ac1.1,ac2.1],tr);let aux_open_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();let final_opening=public_pcs::open(&idx.final_committed,&fc,fv,tr);
 eprintln!("MEMORY_PHASES entry_bits={} table_bits={} aux_commit_s={} main_sumcheck_s={} tree_build_s={} tree_prove_s={} index_open_s={} aux_open_s={} final_open_s={}",k.entry_bits,k.table_bits(),aux_s,main_s,tree_build_s,tree_prove_s,index_open_s,aux_open_s,clock.elapsed().as_secs_f64());
 Proof{auxiliary:aux.key,rounds,endpoints:end,reads,table,memory_endpoints,final_endpoints,opening,auxiliary_opening,final_opening}
}
pub fn verify(k:&Key,row:&[L],col:&[L],rho:[L;3],value:L,p:&Proof,tr:&mut Transcript<'_,H>)->Result<(),String>{
 if !k.valid()||row.len()!=k.row_bits||col.len()!=k.col_bits||p.rounds.len()!=k.entry_bits||p.endpoints.len()!=19||p.memory_endpoints.len()!=19||p.auxiliary.log!=k.entry_bits+2||p.auxiliary.queries!=k.pcs.queries{return Err("memory sparse shape".into());}
 begin(k,row,col,rho,value,tr);tr.absorb(b"memory read values",&p.auxiliary.binding());let(mut r,mut claim)=(vec![],value);
 for q in &p.rounds{if q.len()!=6||q[0]+q[1]!=claim{return Err("sparse sumcheck".into());}let x=tr.round(&ZERO,bytes(q)).field();claim=product_tree::interpolate(q,x);r.push(x);}
 let e=&p.endpoints;if claim!=(0..4).map(|c|e[15+c]).product::<L>()*(0..3).map(|t|rho[t]*e[12+t]).sum::<L>(){return Err("sparse endpoint".into());}let(ic1,ac1)=claims(&r,e,tr);
 let mut ch=tr.round(&ZERO,b"memory tuple compression");let hash=std::array::from_fn(|_|ch.field());bind_products(&p.reads.roots,&p.table.roots,tr)?;
 let(rr,rv)=product_tree::verify(&p.reads,k.entry_bits,tr)?;if rv!=read_leaf(&p.memory_endpoints,&rr[k.entry_bits..],hash){return Err("memory read leaf".into());}let(ic2,ac2)=claims(&rr[..k.entry_bits],&p.memory_endpoints,tr);
 let(rt,tv)=product_tree::verify(&p.table,k.table_bits(),tr)?;if tv!=table_leaf(k,split(k,row,col),&p.final_endpoints,&rt,hash){return Err("memory table leaf".into());}let(fc,fv)=final_claim(&rt[..k.table_bits()],&p.final_endpoints,tr);
 public_pcs::verify_batch(&k.pcs,&[ic1.0,ic2.0],&[ic1.1,ic2.1],&p.opening,tr)?;public_pcs::verify_batch(&p.auxiliary,&[ac1.0,ac2.0],&[ac1.1,ac2.1],&p.auxiliary_opening,tr)?;public_pcs::verify(&k.final_pcs,&fc,fv,&p.final_opening,tr)
}
#[derive(Clone)]
pub struct Contraction {pub rounds:Vec<[L;3]>,pub weight:L,pub matrix:Proof}
impl Contraction {pub fn encode(&self)->Vec<u8>{let mut b=Vec::new();b.extend((self.rounds.len() as u64).to_le_bytes());for s in &self.rounds{b.extend(bytes(s));}b.extend(bytes(&[self.weight]));b.extend(self.matrix.encode());b}}
// The public input vector is supplied by the caller and is allowed O(|x|) work.
pub fn contract_prove(idx:&Index,row:&[L],rho:[L;3],public:&[L],value:L,tr:&mut Transcript<'_,H>)->Contraction{
 tr.absorb(b"public-input contraction",bytes(&[value]));let(mut w,mut v)=(idx.column_weights(row,rho),public.to_vec());assert_eq!(w.len(),v.len());let(mut rounds,mut r,mut s)=(vec![],vec![],value);
 for _ in 0..idx.key.col_bits{let q:[L;3]=[L::ZERO,L::ONE,from_b(omega())].map(|x|(0..w.len()/2).map(|i|(w[2*i]+x*(w[2*i]+w[2*i+1]))*(v[2*i]+x*(v[2*i]+v[2*i+1]))).sum());assert_eq!(q[0]+q[1],s);let x=tr.round(&ZERO,bytes(&q)).field();s=interp(&q,x);r.push(x);rounds.push(q);w=fold_coeffs(&w,x);v=fold_coeffs(&v,x);}
 assert_eq!(s,w[0]*v[0]);tr.absorb(b"public-input matrix value",bytes(&[w[0]]));let matrix=prove(idx,row,&r,rho,w[0],tr);Contraction{rounds,weight:w[0],matrix}
}
pub fn contract_verify(k:&Key,row:&[L],rho:[L;3],public:&[L],value:L,p:&Contraction,tr:&mut Transcript<'_,H>)->Result<(),String>{
 if p.rounds.len()!=k.col_bits||public.len()!=1<<k.col_bits{return Err("public contraction shape".into());}
 tr.absorb(b"public-input contraction",bytes(&[value]));let(mut r,mut s)=(vec![],value);for q in &p.rounds{if q[0]+q[1]!=s{return Err("public contraction sumcheck".into());}let x=tr.round(&ZERO,bytes(q)).field();s=interp(q,x);r.push(x);}
 if s!=p.weight*public_pcs::evaluate(public,&r){return Err("public contraction endpoint".into());}tr.absorb(b"public-input matrix value",bytes(&[p.weight]));verify(k,row,&r,rho,p.weight,&p.matrix,tr)
}
#[cfg(test)]mod tests{
 use super::*;use crate::merkle::Hasher;use rand::{SeedableRng,rngs::StdRng};use crate::field::Random;
 #[test]fn sparse_memory_matches_direct_and_rejects_mutations(){
  let h=Hasher::<H>::default();let mut rng=StdRng::seed_from_u64(72);
  for (rb,cb) in [(0,0),(2,5),(5,3)] {
   let mut entries=vec![];for i in 0..37{entries.push((i%3,(i*7+1)%(1<<rb),(i*11+3)%(1<<cb)));}entries.extend([(0,0,0),(0,0,0)]);
   let idx=index(rb,cb,entries,16);let row:Vec<_>=(0..rb).map(|_|L::random(&mut rng)).collect();let col:Vec<_>=(0..cb).map(|_|L::random(&mut rng)).collect();let rho=std::array::from_fn(|_|L::random(&mut rng));let value=idx.evaluate(&row,&col,rho);
   let p=prove(&idx,&row,&col,rho,value,&mut Transcript::new_global(&h,b"matrix"));let check=|p:&Proof|verify(&idx.key,&row,&col,rho,value,p,&mut Transcript::new_global(&h,b"matrix"));assert!(check(&p).is_ok());
   assert!(verify(&idx.key,&row,&col,rho,value+L::ONE,&p,&mut Transcript::new_global(&h,b"matrix")).is_err());
   for j in [0,4,8,12,15]{let mut bad=p.clone();bad.endpoints[j]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.memory_endpoints[j]+=L::ONE;assert!(check(&bad).is_err());}
   let mut bad=p.clone();bad.auxiliary.root[0]^=1;assert!(check(&bad).is_err());let mut bad=p.clone();bad.reads.roots[0]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.table.layers[0].endpoints[1]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.final_endpoints[0]+=L::ONE;assert!(check(&bad).is_err());
   let mut bad=p.clone();bad.auxiliary_opening.openings[0][0].pair[0]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.final_opening.openings[0][0].pair[0]+=L::ONE;assert!(check(&bad).is_err());
   let public:Vec<_>=(0..1<<cb).map(|_|L::random(&mut rng)).collect();let value=idx.column_weights(&row,rho).iter().zip(&public).map(|(&a,&b)|a*b).sum();let p=contract_prove(&idx,&row,rho,&public,value,&mut Transcript::new_global(&h,b"public"));assert!(contract_verify(&idx.key,&row,rho,&public,value,&p,&mut Transcript::new_global(&h,b"public")).is_ok());let mut wrong=public.clone();wrong[0]+=L::ONE;assert!(contract_verify(&idx.key,&row,rho,&wrong,value,&p,&mut Transcript::new_global(&h,b"public")).is_err());
  }
 }
 #[test]fn leaf_closed_forms_match_explicit_multilinear_tables(){
  let mut rng=StdRng::seed_from_u64(207);
  for (rb,cb) in [(0,0),(1,3),(5,2)] {
   let idx=index(rb,cb,(0..9).map(|i|(i%3,i%(1<<rb),(3*i)%(1<<cb))).collect(),16);
   let k=&idx.key;let n=1<<k.entry_bits;let b=1<<k.table_bits();
   let row:Vec<_>=(0..rb).map(|_|L::random(&mut rng)).collect();let col:Vec<_>=(0..cb).map(|_|L::random(&mut rng)).collect();let queries=split(k,&row,&col);
   // Arbitrary read tables test the affine identity, independently of read consistency.
   let aux=public_pcs::commit((0..4*n).map(|_|L::random(&mut rng)).collect(),16);
   for _ in 0..4 {
    let hash:[L;3]=std::array::from_fn(|_|L::random(&mut rng));
    let rr:Vec<_>=(0..k.entry_bits+3).map(|_|L::random(&mut rng)).collect();
    let mut reads=vec![];
    for c in 0..4 {for h in 0..2 {for i in 0..n {
     reads.push(L::ONE+hash[0]*aux.values[c*n+i]+hash[1]*idx.committed.values[(4+4*h+c)*n+i]+hash[2]*idx.committed.values[c*n+i]);
    }}}
    let e=endpoints(&idx,&aux,&rr[..k.entry_bits]);
    assert_eq!(read_leaf(&e,&rr[k.entry_bits..],hash),public_pcs::evaluate(&reads,&rr));
    let rt:Vec<_>=(0..k.table_bits()+3).map(|_|L::random(&mut rng)).collect();
    let mut tables=vec![];
    for c in 0..4 {for h in 0..2 {for a in 0..b {
     let v=if a<1<<queries[c].len(){chi(a,queries[c])}else{L::ZERO};
     let ts=if h==0{L::ZERO}else{idx.final_committed.values[c*b+a]};
     tables.push(L::ONE+hash[0]*v+hash[1]*ts+hash[2]*label(a));
    }}}
    let end=std::array::from_fn(|c|public_pcs::evaluate(&idx.final_committed.values[c*b..(c+1)*b],&rt[..k.table_bits()]));
    assert_eq!(table_leaf(k,queries,&end,&rt,hash),public_pcs::evaluate(&tables,&rt));
   }
  }
 }
 #[test]fn characteristic_two_counters_and_zero_matrix(){
  let idx=index(2,2,vec![],16);let count=1<<idx.key.entry_bits;
  for i in 0..count{assert_eq!(idx.committed.values[4*count+i],label(i));assert_eq!(idx.committed.values[8*count+i],label(i+1));}assert_ne!(label(2),L::ZERO);assert_ne!(label(3),label(1));
  let h=Hasher::<H>::default();let r=vec![L::ONE;2];let p=prove(&idx,&r,&r,[L::ONE;3],L::ZERO,&mut Transcript::new_global(&h,b"zero"));assert!(verify(&idx.key,&r,&r,[L::ONE;3],L::ZERO,&p,&mut Transcript::new_global(&h,b"zero")).is_ok());
 }
}
