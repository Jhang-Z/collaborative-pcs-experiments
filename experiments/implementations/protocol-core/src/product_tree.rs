//! Batched binary multiplication-tree GKR over L, with full transcript replay.
use crate::{field::{Field,L,from_b,eq_expand},fs::Transcript,code::fold_coeffs,spartan::{omega,eq_eval}};
use binius_hash::Blake3HashSuite as H;
use binius_field::arithmetic_traits::InvertOrZero;
const ZERO:[u8;32]=[0;32];
fn bytes(v:&[L])->&[u8]{bytemuck::cast_slice(v)}
pub fn point(mut i:usize)->L{let(mut x,mut p)=(L::ZERO,L::ONE);while i>0{if i&1==1{x+=p;}p*=from_b(omega());i>>=1;}x}
pub fn interpolate(v:&[L],x:L)->L{let pts:Vec<_>=(0..v.len()).map(point).collect();let mut out=L::ZERO;for i in 0..v.len(){let(mut a,mut b)=(L::ONE,L::ONE);for j in 0..v.len(){if i!=j{a*=x+pts[j];b*=pts[i]+pts[j];}}out+=v[i]*a*b.invert_or_zero();}out}
/// Degree <= factors.len(). The optional transport delivers every worker's contribution.
pub fn round(f:&[Vec<L>])->Vec<L>{
 let n=crate::transport::party_count();let half=f[0].len()/2;let deg=f.len();
 let partials=crate::parallel::map(n,|party|{
  let lo=half*party/n;let hi=half*(party+1)/n;
  let mut q=vec![L::ZERO;deg+1];
  for i in lo..hi {for(t,v)in q.iter_mut().enumerate(){let x=point(t);*v+=f.iter().map(|a|a[2*i]+x*(a[2*i]+a[2*i+1])).product::<L>();}}
  q
 });
 let mut out=vec![L::ZERO;deg+1];for q in crate::transport::values(partials,true){for(x,y)in out.iter_mut().zip(q){*x+=y;}}out
}
#[derive(Clone)]pub struct Layer{pub rounds:Vec<[L;4]>,pub endpoints:[L;2]}
#[derive(Clone)]pub struct Proof{pub roots:[L;8],pub layers:Vec<Layer>}
impl Proof {pub fn encode(&self)->Vec<u8>{let mut b=bytes(&self.roots).to_vec();b.extend((self.layers.len() as u64).to_le_bytes());for l in &self.layers{b.extend((l.rounds.len() as u64).to_le_bytes());for q in &l.rounds{b.extend(bytes(q));}b.extend(bytes(&l.endpoints));}b}}
pub struct Tree{levels:Vec<Vec<L>>,pub roots:[L;8]}
impl Tree{
 pub fn new(leaves:Vec<L>,depth:usize)->Self{
  assert_eq!(leaves.len(),8<<depth);let mut levels=vec![leaves];
  for _ in 0..depth {let v=levels.last().unwrap();let next=crate::parallel::map(v.len()/2,|i|v[2*i]*v[2*i+1]);levels.push(next);}
  let roots=levels.last().unwrap().as_slice().try_into().unwrap();Self{levels,roots}
 }
}
fn start(roots:&[L;8],tr:&mut Transcript<'_,H>)->(Vec<L>,L){let mut ch=tr.round(&ZERO,bytes(roots));let r:Vec<_>=(0..3).map(|_|ch.field()).collect();let s=crate::public_pcs::evaluate(roots,&r);(r,s)}
pub fn prove(tree:Tree,tr:&mut Transcript<'_,H>)->(Proof,Vec<L>,L){
 let(mut r,mut claim)=start(&tree.roots,tr);let mut layers=vec![];
 for level in (0..tree.levels.len()-1).rev(){
  let v=&tree.levels[level];let a=crate::parallel::map(v.len()/2,|i|v[2*i]);let b=crate::parallel::map(v.len()/2,|i|v[2*i+1]);let mut f=vec![a,b,eq_expand(&r)];let mut rounds=vec![];let mut next=vec![];
  for _ in 0..r.len(){let q: [L;4]=round(&f).try_into().unwrap();assert_eq!(q[0]+q[1],claim);let x=tr.round(&ZERO,bytes(&q)).field();claim=interpolate(&q,x);next.push(x);rounds.push(q);crate::parallel::map_mut(&mut f,|_,v|{*v=fold_coeffs(v,x);});}
  let endpoints=[f[0][0],f[1][0]];assert_eq!(claim,endpoints[0]*endpoints[1]*eq_eval(&r,&next));
  let x=tr.round(&ZERO,bytes(&endpoints)).field();claim=endpoints[0]+x*(endpoints[0]+endpoints[1]);r=vec![x];r.extend(next);layers.push(Layer{rounds,endpoints});
 }
 (Proof{roots:tree.roots,layers},r,claim)
}
pub fn verify(p:&Proof,depth:usize,tr:&mut Transcript<'_,H>)->Result<(Vec<L>,L),String>{
 if p.layers.len()!=depth{return Err("product depth".into());}let(mut r,mut claim)=start(&p.roots,tr);
 for layer in &p.layers {
  if layer.rounds.len()!=r.len(){return Err("product round count".into());}let mut next=vec![];
  for q in &layer.rounds{if q[0]+q[1]!=claim{return Err("product sumcheck".into());}let x=tr.round(&ZERO,bytes(q)).field();claim=interpolate(q,x);next.push(x);}
  let e=layer.endpoints;if claim!=e[0]*e[1]*eq_eval(&r,&next){return Err("product endpoint".into());}
  let x=tr.round(&ZERO,bytes(&e)).field();claim=e[0]+x*(e[0]+e[1]);r=vec![x];r.extend(next);
 }
 Ok((r,claim))
}
#[cfg(test)]mod tests{
 use super::*;use crate::{field::Random,merkle::Hasher};use rand::{SeedableRng,rngs::StdRng};
 #[test]fn batch_products_and_mutations(){let h=Hasher::<H>::default();let mut rng=StdRng::seed_from_u64(812);for depth in [0,1,4]{let v:Vec<_>=(0..8<<depth).map(|_|L::random(&mut rng)).collect();let tree=Tree::new(v.clone(),depth);for c in 0..8{assert_eq!(tree.roots[c],v[c*(1<<depth)..(c+1)*(1<<depth)].iter().copied().product());}let(p,r,s)=prove(tree,&mut Transcript::new_global(&h,b"product test"));assert_eq!(p.layers.iter().map(|l|l.rounds.len()).sum::<usize>(),depth*(depth.saturating_sub(1))/2+3*depth);let(r2,s2)=verify(&p,depth,&mut Transcript::new_global(&h,b"product test")).unwrap();assert_eq!((r,s),(r2.clone(),s2));assert_eq!(s2,crate::public_pcs::evaluate(&v,&r2));if depth>0{let mut bad=p.clone();bad.layers[0].endpoints[0]+=L::ONE;assert!(verify(&bad,depth,&mut Transcript::new_global(&h,b"product test")).is_err());}}}
}
