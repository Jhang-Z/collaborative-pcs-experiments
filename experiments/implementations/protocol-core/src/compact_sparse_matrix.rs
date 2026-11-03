//! Pappas/Spartan read-only memory sparse evaluation, adapted to characteristic two.
//! Compact generic index: multiplicative time labels and implicit sorted matrix intervals.
//! The legacy sparse_matrix module remains the verifier for earlier indexed proofs.
use crate::{field::{Field,L,from_words,basis,chi,eq_expand},fs::Transcript,
 public_pcs::{self,Committed},product_tree::{self,Tree},code::fold_coeffs,spartan::{omega,interp,eq_eval},field::from_b};
use binius_hash::Blake3HashSuite as H;
use std::collections::BTreeSet;
const ZERO:[u8;32]=[0;32];
fn bytes(x:&[L])->&[u8]{bytemuck::cast_slice(x)}
fn label(i:usize)->L{from_words([i as u128,0])}

/// GF(2^128)* generator has order2^128-1; entry counts fit below2^64.
/// Multiplication is linear over L, so WR(r)=g*RD(r) also at off-cube points.
pub(crate) fn time_step()->L{from_b(crate::field::B::MULTIPLICATIVE_GENERATOR)}
fn prefix(n:usize,r:&[L])->L{
 assert!(r.len()<usize::BITS as usize&&n<=1usize<<r.len());
 if n==1usize<<r.len(){return L::ONE;}
 let(mut value,mut equal)=(L::ZERO,L::ONE);
 for j in (0..r.len()).rev(){if n>>j&1==1{value+=equal*(L::ONE+r[j]);equal*=r[j];}else{equal*=L::ONE+r[j];}}
 value
}
#[derive(Clone,Debug)]
pub struct Key {pub row_bits:usize,pub col_bits:usize,pub entry_bits:usize,pub channel_bits:usize,pub counts:[usize;3],pub pcs:public_pcs::Key,pub final_pcs:public_pcs::Key}
impl Key {
 pub fn channels(&self)->usize{8}
 pub fn mix(&self,i:usize,rho:[L;3])->L{let mut end=0;for(t,&count)in self.counts.iter().enumerate(){end+=count;if i<end{return rho[t];}}L::ZERO}
 pub fn mix_eval(&self,r:&[L],rho:[L;3])->L{let mut end=0;let mut previous=L::ZERO;let mut value=L::ZERO;for(t,&count)in self.counts.iter().enumerate(){end+=count;let next=prefix(end,r);value+=rho[t]*(previous+next);previous=next;}value}
 pub fn chunks(&self)->[usize;4]{[self.row_bits/2,self.row_bits-self.row_bits/2,self.col_bits/2,self.col_bits-self.col_bits/2]}
 pub fn product_bits(&self)->usize{self.entry_bits.max(self.table_bits())+1}
 pub fn table_bits(&self)->usize{*self.chunks().iter().max().unwrap().max(&2)}
 pub fn binding(&self)->Vec<u8>{let mut b=self.pcs.binding();for n in [self.row_bits,self.col_bits,self.entry_bits,self.channel_bits]{b.extend((n as u64).to_le_bytes());}for count in self.counts{b.extend((count as u64).to_le_bytes());}b.extend(self.final_pcs.binding());b}
 pub fn valid(&self)->bool{self.row_bits<usize::BITS as usize&&self.col_bits<usize::BITS as usize&&self.entry_bits>=2&&self.entry_bits<usize::BITS as usize-4&&self.channel_bits==3&&self.entry_bits+3==self.pcs.log&&self.counts.iter().try_fold(0usize,|a,&b|a.checked_add(b)).is_some_and(|n|n<=1usize<<self.entry_bits)&&self.final_pcs.log==self.table_bits()+2&&self.pcs.queries==self.final_pcs.queries&&self.pcs.queries>0}
}
pub struct Index {pub key:Key,pub entries:Vec<(usize,usize,usize)>,pub committed:Committed,pub final_committed:Committed,addresses:[Vec<usize>;4]}
pub struct IndexData {row_bits:usize,col_bits:usize,queries:usize,counts:[usize;3],entries:Vec<(usize,usize,usize)>,addresses:[Vec<usize>;4],values:Vec<L>,finals:Vec<L>}
impl IndexData {pub fn into_tables(self)->(usize,usize,usize,usize,[usize;3],Vec<L>,Vec<L>){(self.row_bits,self.col_bits,self.queries,self.entries.len().max(4).next_power_of_two(),self.counts,self.values,self.finals)}}
#[derive(Clone)]
pub struct Proof {
 pub auxiliary:public_pcs::Key,pub rounds:Vec<Vec<L>>,pub endpoints:Vec<L>,
 pub products:product_tree::Proof,pub memory_endpoints:Vec<L>,pub final_endpoints:[L;4],
 pub opening:public_pcs::Proof,pub auxiliary_opening:public_pcs::Proof,pub final_opening:public_pcs::Proof,
}
impl Proof {pub fn encode(&self)->Vec<u8>{let mut b=self.auxiliary.binding();b.extend((self.rounds.len() as u64).to_le_bytes());for q in &self.rounds{b.extend(bytes(q));}b.extend(bytes(&self.endpoints));b.extend(self.products.encode());b.extend(bytes(&self.memory_endpoints));b.extend(bytes(&self.final_endpoints));b.extend(self.opening.encode());b.extend(self.auxiliary_opening.encode());b.extend(self.final_opening.encode());b}}
pub fn index_data(row_bits:usize,col_bits:usize,entries:Vec<(usize,usize,usize)>,queries:usize)->IndexData{
 assert!(row_bits<usize::BITS as usize&&col_bits<usize::BITS as usize);
 let mut set=BTreeSet::new();for e in entries{assert!(e.0<3&&e.1<1<<row_bits&&e.2<1<<col_bits);if !set.insert(e){set.remove(&e);}}
 let entries:Vec<_>=set.into_iter().collect();let count=entries.len().max(4).next_power_of_two();let chunks=[row_bits/2,row_bits-row_bits/2,col_bits/2,col_bits-col_bits/2];let table_bits=(*chunks.iter().max().unwrap()).max(2);let b=1<<table_bits;
 let mut values=vec![L::ZERO;8*count];let mut finals=vec![L::ONE;4*b];let mut counts=[0usize;3];let mut addresses:[Vec<usize>;4]=std::array::from_fn(|_|vec![0;count]);
 for(i,&(t,row,col))in entries.iter().enumerate(){addresses[0][i]=row&((1<<chunks[0])-1);addresses[1][i]=row>>chunks[0];addresses[2][i]=col&((1<<chunks[2])-1);addresses[3][i]=col>>chunks[2];counts[t]+=1;}
 for c in 0..4 {let mut counters=vec![L::ONE;b];for i in 0..count{let a=addresses[c][i];values[c*count+i]=label(a);values[(4+c)*count+i]=counters[a];counters[a]*=time_step();}finals[c*b..(c+1)*b].copy_from_slice(&counters);}
 IndexData{row_bits,col_bits,queries,counts,entries,addresses,values,finals}
}
pub fn index(row_bits:usize,col_bits:usize,entries:Vec<(usize,usize,usize)>,queries:usize)->Index{
 let IndexData{row_bits,col_bits,queries,counts,entries,addresses,values,finals}=index_data(row_bits,col_bits,entries,queries);let count=entries.len().max(4).next_power_of_two();
 let committed=public_pcs::commit(values,queries);let final_committed=public_pcs::commit(finals,queries);let key=Key{row_bits,col_bits,entry_bits:count.trailing_zeros() as usize,channel_bits:3,counts,pcs:committed.key.clone(),final_pcs:final_committed.key.clone()};Index{key,entries,committed,final_committed,addresses}
}
impl Index {
 pub fn evaluate(&self,row:&[L],col:&[L],rho:[L;3])->L{self.entries.iter().map(|&(t,i,j)|rho[t]*chi(i,row)*chi(j,col)).sum()}
 pub fn column_weights(&self,row:&[L],rho:[L;3])->Vec<L>{let mut w=vec![L::ZERO;1<<self.key.col_bits];for &(t,i,j) in &self.entries{w[j]+=rho[t]*chi(i,row);}w}
}
pub(crate) fn begin(key:&Key,row:&[L],col:&[L],rho:[L;3],value:L,tr:&mut Transcript<'_,H>){tr.absorb(b"compact memory sparse index v2",&key.binding());tr.absorb(b"sparse row",bytes(row));tr.absorb(b"sparse column",bytes(col));tr.absorb(b"sparse mix/value",bytes(&[rho[0],rho[1],rho[2],value]));}
fn split<'a>(k:&Key,row:&'a[L],col:&'a[L])->[&'a[L];4]{[&row[..k.row_bits/2],&row[k.row_bits/2..],&col[..k.col_bits/2],&col[k.col_bits/2..]]}
fn endpoints(idx:&Index,aux:&Committed,r:&[L])->Vec<L>{let n=1<<idx.key.entry_bits;crate::parallel::map(12,|j|if j<8{public_pcs::evaluate(&idx.committed.values[j*n..(j+1)*n],r)}else{public_pcs::evaluate(&aux.values[(j-8)*n..(j-7)*n],r)})}
// Bind all endpoint values before sampling their channel-combination points.
pub(crate) fn claims(r:&[L],e:&[L],tr:&mut Transcript<'_,H>)->((Vec<L>,L),(Vec<L>,L)){
 let mut ch=tr.round(&ZERO,bytes(e));let ri:Vec<_>=(0..3).map(|_|ch.field()).collect();let ra:Vec<_>=(0..2).map(|_|ch.field()).collect();
 let vi=e[..8].iter().enumerate().map(|(i,&v)|chi(i,&ri)*v).sum();let va=e[8..].iter().enumerate().map(|(i,&v)|chi(i,&ra)*v).sum();let mut pi=r.to_vec();pi.extend(ri);let mut pa=r.to_vec();pa.extend(ra);((pi,vi),(pa,va))
}
pub(crate) fn read_leaf(e:&[L],r:&[L],hash:[L;3])->L{(0..4).map(|c|chi(c,&r[1..])*(L::ONE+hash[0]*e[8+c]+hash[1]*(e[4+c]*(L::ONE+r[0]*(L::ONE+time_step())))+hash[2]*e[c])).sum()}
pub(crate) fn table_leaf(k:&Key,queries:[&[L];4],e:&[L;4],r:&[L],hash:[L;3])->L{let n=k.table_bits();let addr:L=r[..n].iter().enumerate().map(|(j,&x)|basis(j)*x).sum();(0..4).map(|c|{let q=queries[c];let v=eq_eval(q,&r[..q.len()])*r[q.len()..n].iter().map(|&x|L::ONE+x).product::<L>();chi(c,&r[n+1..])*(L::ONE+hash[0]*v+hash[1]*(L::ONE+r[n]*(L::ONE+e[c]))+hash[2]*addr)}).sum()}
// Each root combines reads with the opposite table parity. Pairwise equality
// is exactly RD*Final=WR*Initial, including multiplicative-one padding.
pub(crate) fn bind_products(roots:&[L;8],tr:&mut Transcript<'_,H>)->Result<(),String>{for c in 0..4{if roots[2*c]!=roots[2*c+1]{return Err("memory multiset products".into());}}tr.absorb(b"combined memory products",bytes(roots));Ok(())}
pub(crate) fn product_leaf(k:&Key,queries:[&[L];4],reads:&[L],finals:&[L;4],r:&[L],hash:[L;3])->L{
 let m=k.product_bits()-1;let channels=&r[m+1..];
 let read=L::ONE+chi(0,&r[k.entry_bits..m])*(read_leaf(reads,channels,hash)+L::ONE);
 let mut table_point=r[..k.table_bits()].to_vec();table_point.extend_from_slice(channels);table_point[k.table_bits()]+=L::ONE;
 let table=L::ONE+chi(0,&r[k.table_bits()..m])*(table_leaf(k,queries,finals,&table_point,hash)+L::ONE);
 read+r[m]*(read+table)
}
pub(crate) fn final_claim(r:&[L],e:&[L;4],tr:&mut Transcript<'_,H>)->(Vec<L>,L){let mut ch=tr.round(&ZERO,bytes(e));let rc:Vec<_>=(0..2).map(|_|ch.field()).collect();let value=public_pcs::evaluate(e,&rc);let mut p=r.to_vec();p.extend(rc);(p,value)}
pub fn prove(idx:&Index,row:&[L],col:&[L],rho:[L;3],value:L,tr:&mut Transcript<'_,H>)->Proof{
 let clock=std::time::Instant::now();let k=&idx.key;assert_eq!((row.len(),col.len()),(k.row_bits,k.col_bits));begin(k,row,col,rho,value,tr);let count=1<<k.entry_bits;let queries=split(k,row,col);
 let tables:[Vec<L>;4]=queries.map(eq_expand);
 let aux_values=crate::parallel::map(4*count,|i|tables[i/count][idx.addresses[i/count][i%count]]);let aux=public_pcs::commit(aux_values,k.pcs.queries);tr.absorb(b"memory read values",&aux.key.binding());let aux_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();
 let mut f:Vec<Vec<L>>=(0..4).map(|c|aux.values[c*count..(c+1)*count].to_vec()).collect();f.push(crate::parallel::map(count,|i|k.mix(i,rho)));
 let(mut rounds,mut r,mut claim)=(vec![],vec![],value);
 for _ in 0..k.entry_bits{let q=product_tree::round(&f);assert_eq!(q[0]+q[1],claim);let x=tr.round(&ZERO,bytes(&q)).field();claim=product_tree::interpolate(&q,x);r.push(x);rounds.push(q);crate::parallel::map_mut(&mut f,|_,v|{*v=fold_coeffs(v,x);});}
 let end=endpoints(idx,&aux,&r);assert_eq!(claim,(0..4).map(|c|end[8+c]).product::<L>()*k.mix_eval(&r,rho));let(ic1,ac1)=claims(&r,&end,tr);let main_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();
 let mut ch=tr.round(&ZERO,b"memory tuple compression");let hash:[L;3]=std::array::from_fn(|_|ch.field());
 let b=1<<k.table_bits();let width=1<<(k.product_bits()-1);
 let products=Tree::new(crate::parallel::map(16*width,|i|{
  let channel=i/(2*width);let c=channel/2;let j=i%width;
  if i/width%2==0 {
   if j>=count{return L::ONE;}let step=if channel%2==0{L::ONE}else{time_step()};
   L::ONE+hash[0]*aux.values[c*count+j]+hash[1]*step*idx.committed.values[(4+c)*count+j]+hash[2]*idx.committed.values[c*count+j]
  }else{
   if j>=b{return L::ONE;}
   L::ONE+hash[0]*tables[c].get(j).copied().unwrap_or(L::ZERO)+hash[2]*label(j)+hash[1]*if channel%2==0{idx.final_committed.values[c*b+j]}else{L::ONE}
  }
 }),k.product_bits());
 let tree_build_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();bind_products(&products.roots,tr).unwrap();let(products,rr,rv)=product_tree::prove(products,tr);
 let memory_endpoints=endpoints(idx,&aux,&rr[..k.entry_bits]);
 let final_endpoints=std::array::from_fn(|c|public_pcs::evaluate(&idx.final_committed.values[c*b..(c+1)*b],&rr[..k.table_bits()]));
 assert_eq!(rv,product_leaf(k,queries,&memory_endpoints,&final_endpoints,&rr,hash));
 let(ic2,ac2)=claims(&rr[..k.entry_bits],&memory_endpoints,tr);let(fc,fv)=final_claim(&rr[..k.table_bits()],&final_endpoints,tr);let tree_prove_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();
 let opening=public_pcs::open_batch(&idx.committed,&[ic1.0,ic2.0],&[ic1.1,ic2.1],tr);let index_open_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();let auxiliary_opening=public_pcs::open_batch(&aux,&[ac1.0,ac2.0],&[ac1.1,ac2.1],tr);let aux_open_s=clock.elapsed().as_secs_f64();let clock=std::time::Instant::now();let final_opening=public_pcs::open(&idx.final_committed,&fc,fv,tr);
 eprintln!("MEMORY_PHASES entry_bits={} table_bits={} aux_commit_s={} main_sumcheck_s={} tree_build_s={} tree_prove_s={} index_open_s={} aux_open_s={} final_open_s={}",k.entry_bits,k.table_bits(),aux_s,main_s,tree_build_s,tree_prove_s,index_open_s,aux_open_s,clock.elapsed().as_secs_f64());
 Proof{auxiliary:aux.key,rounds,endpoints:end,products,memory_endpoints,final_endpoints,opening,auxiliary_opening,final_opening}
}
pub fn verify(k:&Key,row:&[L],col:&[L],rho:[L;3],value:L,p:&Proof,tr:&mut Transcript<'_,H>)->Result<(),String>{
 if !k.valid()||row.len()!=k.row_bits||col.len()!=k.col_bits||p.rounds.len()!=k.entry_bits||p.endpoints.len()!=12||p.memory_endpoints.len()!=12||p.auxiliary.log!=k.entry_bits+2||p.auxiliary.queries!=k.pcs.queries{return Err("memory sparse shape".into());}
 begin(k,row,col,rho,value,tr);tr.absorb(b"memory read values",&p.auxiliary.binding());let(mut r,mut claim)=(vec![],value);
 for q in &p.rounds{if q.len()!=6||q[0]+q[1]!=claim{return Err("sparse sumcheck".into());}let x=tr.round(&ZERO,bytes(q)).field();claim=product_tree::interpolate(q,x);r.push(x);}
 let e=&p.endpoints;if claim!=(0..4).map(|c|e[8+c]).product::<L>()*k.mix_eval(&r,rho){return Err("sparse endpoint".into());}let(ic1,ac1)=claims(&r,e,tr);
 let mut ch=tr.round(&ZERO,b"memory tuple compression");let hash=std::array::from_fn(|_|ch.field());bind_products(&p.products.roots,tr)?;
 let(rr,rv)=product_tree::verify(&p.products,k.product_bits(),tr)?;
 if rv!=product_leaf(k,split(k,row,col),&p.memory_endpoints,&p.final_endpoints,&rr,hash){return Err("combined memory leaf".into());}
 let(ic2,ac2)=claims(&rr[..k.entry_bits],&p.memory_endpoints,tr);let(fc,fv)=final_claim(&rr[..k.table_bits()],&p.final_endpoints,tr);
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

 #[test]fn multiplicative_labels_have_full_subfield_order(){
  let order=u128::MAX;let g=time_step();let pow=|n:u128|g.pow([n as u64,(n>>64)as u64]);
  assert_eq!(pow(order),L::ONE);
  for p in [3u128,5,17,257,641,65537,274177,6700417,67280421310721]{assert_ne!(pow(order/p),L::ONE);}
 }
 #[test]fn implicit_coefficients_match_expanded_intervals(){
  let mut rng=StdRng::seed_from_u64(730);
  for e in 0..8{let r:Vec<_>=(0..e).map(|_|L::random(&mut rng)).collect();
   for n in 0..=1<<e{assert_eq!(prefix(n,&r),(0..n).map(|i|chi(i,&r)).sum::<L>());}
  }
  let idx=index(3,3,vec![(0,0,1),(0,1,2),(2,3,4)],16);
  let r=vec![label(19);idx.key.entry_bits];let rho=[label(3),label(5),label(7)];
  assert_eq!(idx.key.mix_eval(&r,rho),(0..1<<r.len()).map(|i|chi(i,&r)*idx.key.mix(i,rho)).sum());
  let mut bad=idx.key.clone();bad.counts=[usize::MAX,1,0];assert!(!bad.valid());
 }
 #[test]fn sparse_memory_matches_direct_and_rejects_mutations(){
  let h=Hasher::<H>::default();let mut rng=StdRng::seed_from_u64(72);
  for (rb,cb) in [(0,0),(2,5),(5,3),(9,1)] {
   let mut entries=vec![];for i in 0..37{entries.push((i%3,(i*7+1)%(1<<rb),(i*11+3)%(1<<cb)));}entries.extend([(0,0,0),(0,0,0)]);
   let idx=index(rb,cb,entries,16);let row:Vec<_>=(0..rb).map(|_|L::random(&mut rng)).collect();let col:Vec<_>=(0..cb).map(|_|L::random(&mut rng)).collect();let rho=std::array::from_fn(|_|L::random(&mut rng));let value=idx.evaluate(&row,&col,rho);
   let p=prove(&idx,&row,&col,rho,value,&mut Transcript::new_global(&h,b"matrix"));let check=|p:&Proof|verify(&idx.key,&row,&col,rho,value,p,&mut Transcript::new_global(&h,b"matrix"));assert!(check(&p).is_ok());
   assert!(verify(&idx.key,&row,&col,rho,value+L::ONE,&p,&mut Transcript::new_global(&h,b"matrix")).is_err());
   for j in [0,4,7,8,11]{let mut bad=p.clone();bad.endpoints[j]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.memory_endpoints[j]+=L::ONE;assert!(check(&bad).is_err());}
   let mut bad=p.clone();bad.auxiliary.root[0]^=1;assert!(check(&bad).is_err());let mut bad=p.clone();bad.products.roots[0]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.products.roots[0]+=L::ONE;bad.products.roots[1]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.products.layers[0].endpoints[1]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.final_endpoints[0]+=L::ONE;assert!(check(&bad).is_err());
   let mut bad=p.clone();bad.auxiliary_opening.openings[0][0].pair[0]+=L::ONE;assert!(check(&bad).is_err());let mut bad=p.clone();bad.final_opening.openings[0][0].pair[0]+=L::ONE;assert!(check(&bad).is_err());
   let public:Vec<_>=(0..1<<cb).map(|_|L::random(&mut rng)).collect();let value=idx.column_weights(&row,rho).iter().zip(&public).map(|(&a,&b)|a*b).sum();let p=contract_prove(&idx,&row,rho,&public,value,&mut Transcript::new_global(&h,b"public"));assert!(contract_verify(&idx.key,&row,rho,&public,value,&p,&mut Transcript::new_global(&h,b"public")).is_ok());let mut wrong=public.clone();wrong[0]+=L::ONE;assert!(contract_verify(&idx.key,&row,rho,&wrong,value,&p,&mut Transcript::new_global(&h,b"public")).is_err());
  }
 }
 #[test]fn leaf_closed_forms_match_explicit_multilinear_tables(){
  let mut rng=StdRng::seed_from_u64(207);
  for (rb,cb) in [(0,0),(1,3),(5,2),(11,1)] {
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
     reads.push(L::ONE+hash[0]*aux.values[c*n+i]+hash[1]*(if h==0{L::ONE}else{time_step()})*idx.committed.values[(4+c)*n+i]+hash[2]*idx.committed.values[c*n+i]);
    }}}
    let e=endpoints(&idx,&aux,&rr[..k.entry_bits]);
    assert_eq!(read_leaf(&e,&rr[k.entry_bits..],hash),public_pcs::evaluate(&reads,&rr));
    let rt:Vec<_>=(0..k.table_bits()+3).map(|_|L::random(&mut rng)).collect();
    let mut tables=vec![];
    for c in 0..4 {for h in 0..2 {for a in 0..b {
     let v=if a<1<<queries[c].len(){chi(a,queries[c])}else{L::ZERO};
     let ts=if h==0{L::ONE}else{idx.final_committed.values[c*b+a]};
     tables.push(L::ONE+hash[0]*v+hash[1]*ts+hash[2]*label(a));
    }}}
    let end=std::array::from_fn(|c|public_pcs::evaluate(&idx.final_committed.values[c*b..(c+1)*b],&rt[..k.table_bits()]));
    assert_eq!(table_leaf(k,queries,&end,&rt,hash),public_pcs::evaluate(&tables,&rt));
    let width=1<<(k.product_bits()-1);let mut combined=vec![L::ONE;16*width];
    for channel in 0..8 {
     combined[2*channel*width..2*channel*width+n].copy_from_slice(&reads[channel*n..(channel+1)*n]);
     combined[(2*channel+1)*width..(2*channel+1)*width+b].copy_from_slice(&tables[(channel^1)*b..((channel^1)+1)*b]);
    }
    let r:Vec<_>=(0..k.product_bits()+3).map(|_|L::random(&mut rng)).collect();
    let re=endpoints(&idx,&aux,&r[..k.entry_bits]);
    let fe=std::array::from_fn(|c|public_pcs::evaluate(&idx.final_committed.values[c*b..(c+1)*b],&r[..k.table_bits()]));
    assert_eq!(product_leaf(k,queries,&re,&fe,&r,hash),public_pcs::evaluate(&combined,&r));
   }
  }
 }
 #[test]fn characteristic_two_counters_and_zero_matrix(){
  let idx=index(2,2,vec![],16);let count=1<<idx.key.entry_bits;
  for i in 0..count{assert_eq!(idx.committed.values[4*count+i],time_step().pow([i as u64]));}assert_ne!(label(2),L::ZERO);assert_ne!(label(3),label(1));
  let h=Hasher::<H>::default();let r=vec![L::ONE;2];let p=prove(&idx,&r,&r,[L::ONE;3],L::ZERO,&mut Transcript::new_global(&h,b"zero"));assert!(verify(&idx.key,&r,&r,[L::ONE;3],L::ZERO,&p,&mut Transcript::new_global(&h,b"zero")).is_ok());
 }
}
