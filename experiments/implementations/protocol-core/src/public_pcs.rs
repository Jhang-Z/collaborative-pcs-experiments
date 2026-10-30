//! Non-hiding L-valued row Fold for a fixed public circuit index.
//! No witness, masks, table-sized verifier weights, or preexpanded verifier NTT.
use crate::{code::{RowCode,fold_coeffs},field::{Field,L,eq_expand},fs::Transcript,
 merkle::{Hash,Hasher,Tree,root_from_path},spartan::eq_eval};
use binius_hash::Blake3HashSuite as H;
const ZERO:Hash=[0;32];
const ROLE:u64=3;
fn bytes(x:&[L])->&[u8]{bytemuck::cast_slice(x)}
#[derive(Clone,Debug)]
pub struct Key {pub log:usize,pub queries:usize,pub root:Hash}
impl Key {
 pub fn binding(&self)->Vec<u8>{let mut b=Vec::new();b.extend((self.log as u64).to_le_bytes());b.extend((self.queries as u64).to_le_bytes());b.extend(self.root);b}
 fn valid(&self)->bool{self.log>=4&&self.log<usize::BITS as usize-3&&self.queries>0}
}
pub struct Committed {pub key:Key,pub values:Vec<L>,code:RowCode,cw:Vec<L>,tree:Tree}
#[derive(Clone)]
pub struct Query {pub pair:[L;2],pub path:Vec<Hash>}
#[derive(Clone)]
pub struct Proof {pub roots:Vec<Hash>,pub rounds:Vec<(L,L)>,pub tail:Vec<L>,pub openings:Vec<Vec<Query>>}
impl Proof {
 pub fn encode(&self)->Vec<u8>{let mut b=Vec::new();for n in [self.roots.len(),self.rounds.len(),self.tail.len(),self.openings.len()]{b.extend((n as u64).to_le_bytes());}for h in &self.roots {b.extend(h);}for &(x,y) in &self.rounds{b.extend(bytes(&[x,y]));}b.extend(bytes(&self.tail));for q in &self.openings{b.extend((q.len() as u64).to_le_bytes());for o in q{b.extend(bytes(&o.pair));b.extend((o.path.len() as u64).to_le_bytes());for h in &o.path{b.extend(h);}}}b}
}
fn tree(cw:&[L],layer:usize)->Tree{let h=Hasher::<H>::scoped(ROLE).at_layer(layer as u64);Tree::build(&h,crate::parallel::map(cw.len()/2, |i|h.leaf(layer as u64,i as u64,bytes(&cw[2*i..2*i+2]),&[])))}
pub fn commit(values:Vec<L>,queries:usize)->Committed{
 assert!(values.len().is_power_of_two()&&values.len()>=16&&queries>0);
 let log=values.len().trailing_zeros() as usize;let code=RowCode::new(log,2);let cw=code.encode(&values);let tree=tree(&cw,0);
 let key=Key{log,queries,root:tree.root()};Committed{key,values,code,cw,tree}
}
fn begin_batch(key:&Key,points:&[Vec<L>],values:&[L],tr:&mut Transcript<'_,H>)->Vec<L>{
 tr.absorb(b"public batch opening key",&key.binding());
 tr.absorb(b"public batch count",&(points.len() as u64).to_le_bytes());
 for (p,&v) in points.iter().zip(values){tr.absorb(b"public batch point",bytes(p));tr.absorb(b"public batch value",bytes(&[v]));}
 let mut ch=tr.round(&ZERO,b"public batch coefficients");(0..points.len()).map(|_|ch.field()).collect()
}
pub fn evaluate(v:&[L],r:&[L])->L{assert_eq!(v.len(),1<<r.len());{let mut f=v.to_vec();for &x in r{f=fold_coeffs(&f,x);}f[0]}}
pub fn open(c:&Committed,point:&[L],value:L,tr:&mut Transcript<'_,H>)->Proof{
 open_batch(c,&[point.to_vec()],&[value],tr)
}
pub fn open_batch(c:&Committed,points:&[Vec<L>],values:&[L],tr:&mut Transcript<'_,H>)->Proof{
 assert!(!points.is_empty()&&points.len()==values.len()&&points.iter().all(|p|p.len()==c.key.log));
 let a=begin_batch(&c.key,points,values,tr);let value:L=a.iter().zip(values).map(|(&a,&v)|a*v).sum();
 let mut w=vec![L::ZERO;c.values.len()];for(p,&a)in points.iter().zip(&a){let e=eq_expand(p);for(x,y)in w.iter_mut().zip(e){*x+=a*y;}}
 let folds=c.key.log-3;let mut f=c.values.clone();let mut cw=c.cw.clone();
 let(mut roots,mut rounds,mut trees,mut words)=(vec![c.key.root],vec![],vec![],vec![]);let mut s=value;
 for j in 0..folds {
  let mut a=L::ZERO;let mut b=L::ZERO;
  let chunks=(f.len()/2).div_ceil(4096);
  let partials=crate::parallel::map(chunks, |chunk| {let(mut a,mut b)=(L::ZERO,L::ZERO);for i in chunk*4096..((chunk+1)*4096).min(f.len()/2){let x=&f[2*i..2*i+2];let y=&w[2*i..2*i+2];a+=x[0]*y[0];b+=(x[1]+x[0])*(y[1]+y[0]);}(a,b)});
  for(x,y)in partials{a+=x;b+=y;}
  rounds.push((a,b));let r=tr.round(&roots[j],bytes(&[a,b])).field();assert_ne!(r,L::ONE);
  s=a+(s+b)*r+b*r*r;f=fold_coeffs(&f,r);w=fold_coeffs(&w,r);
  words.push(cw.clone());cw=c.code.fold(&cw,r);
  if j+1<folds {let t=tree(&cw,j+1);roots.push(t.root());trees.push(t);}
 }
 assert_eq!(s,f.iter().zip(w).map(|(&x,y)|x*y).sum::<L>());
 let mut ch=tr.round(&ZERO,bytes(&f));let qs:Vec<_>=(0..c.key.queries).map(|_|ch.bits((c.key.log+1) as u32) as usize).collect();
 let openings=qs.into_iter().map(|q|(0..folds).map(|j|{let i=q>>j;Query{pair:[words[j][2*i],words[j][2*i+1]],path:if j==0 {c.tree.path(i)}else{trees[j-1].path(i)}}}).collect()).collect();
 let proof=Proof{roots,rounds,tail:f,openings};tr.absorb(b"public-index opening",&proof.encode());proof
}
pub fn verify(key:&Key,point:&[L],value:L,p:&Proof,tr:&mut Transcript<'_,H>)->Result<(),String>{
 verify_batch(key,&[point.to_vec()],&[value],p,tr)
}
pub fn verify_batch(key:&Key,points:&[Vec<L>],values:&[L],p:&Proof,tr:&mut Transcript<'_,H>)->Result<(),String>{
 if !key.valid()||points.is_empty()||points.len()!=values.len()||points.iter().any(|p|p.len()!=key.log){return Err("public key/point shape".into());}
 let folds=key.log-3;
 if p.roots.len()!=folds||p.roots[0]!=key.root||p.rounds.len()!=folds||p.tail.len()!=8||p.openings.len()!=key.queries{return Err("public proof shape/root".into());}
 let a=begin_batch(key,points,values,tr);let value:L=a.iter().zip(values).map(|(&a,&v)|a*v).sum();let(mut s,mut r)=(value,vec![]);
 for j in 0..folds{let(a,b)=p.rounds[j];let x=tr.round(&p.roots[j],bytes(&[a,b])).field();if x==L::ONE{return Err("public excluded challenge".into());}s=a+(s+b)*x+b*x*x;r.push(x);}
 let endpoint=points.iter().zip(&a).map(|(point,&a)|a*eq_eval(&r,&point[..folds])*evaluate(&p.tail,&point[folds..])).sum::<L>();
 if s!=endpoint{return Err("public Fold endpoint".into());}
 let code=RowCode::compact(key.log,2);let tail=code.encode(&p.tail);
 let mut ch=tr.round(&ZERO,bytes(&p.tail));
 for ops in &p.openings{
  let q=ch.bits((key.log+1) as u32) as usize;if ops.len()!=folds{return Err("public query shape".into());}
  for j in 0..folds{let i=q>>j;let op=&ops[j];let h=Hasher::<H>::scoped(ROLE).at_layer(j as u64);
   if op.path.len()!=key.log+1-j||root_from_path(&h,h.leaf(j as u64,i as u64,bytes(&op.pair),&[]),i,&op.path)!=p.roots[j]{return Err("public Merkle path".into());}
   let next=if j+1<folds{ops[j+1].pair[i&1]}else{tail[i]};
   if code.fold_pair(key.log+2-j,i,op.pair[0],op.pair[1],r[j])!=next{return Err("public fold consistency".into());}
  }
 }
 tr.absorb(b"public-index opening",&p.encode());Ok(())
}
#[cfg(test)]mod tests{
 use super::*;use crate::{field::{Random,from_words},params::Params,setup::Setup};use rand::{SeedableRng,rngs::StdRng};
 #[test]fn public_opening_and_mutations(){let mut rng=StdRng::seed_from_u64(501);let c=commit((0..128).map(|_|L::random(&mut rng)).collect(),32);let r:Vec<_>=(0..7).map(|_|L::random(&mut rng)).collect();let v=evaluate(&c.values,&r);let h=Hasher::<H>::default();let p=open(&c,&r,v,&mut Transcript::new_global(&h,b"test"));assert!(verify(&c.key,&r,v,&p,&mut Transcript::new_global(&h,b"test")).is_ok());assert!(verify(&c.key,&r,v+L::ONE,&p,&mut Transcript::new_global(&h,b"test")).is_err());let mut bad=p.clone();bad.openings[0][0].pair[0]+=L::ONE;assert!(verify(&c.key,&r,v,&bad,&mut Transcript::new_global(&h,b"test")).is_err());let mut bad=c.key.clone();bad.root[0]^=1;assert!(verify(&bad,&r,v,&p,&mut Transcript::new_global(&h,b"test")).is_err());}
 #[test]fn multiple_points_share_one_fold(){let mut rng=StdRng::seed_from_u64(507);let c=commit((0..128).map(|_|L::random(&mut rng)).collect(),16);let points:Vec<Vec<L>>=(0..3).map(|_|(0..7).map(|_|L::random(&mut rng)).collect()).collect();let values:Vec<_>=points.iter().map(|p|evaluate(&c.values,p)).collect();let h=Hasher::<H>::default();let p=open_batch(&c,&points,&values,&mut Transcript::new_global(&h,b"batch"));assert!(verify_batch(&c.key,&points,&values,&p,&mut Transcript::new_global(&h,b"batch")).is_ok());for i in 0..3{let mut bad=values.clone();bad[i]+=L::ONE;assert!(verify_batch(&c.key,&points,&bad,&p,&mut Transcript::new_global(&h,b"batch")).is_err());let mut bad=points.clone();bad[i][0]+=L::ONE;assert!(verify_batch(&c.key,&bad,&values,&p,&mut Transcript::new_global(&h,b"batch")).is_err());}}
 #[test]fn billion_column_verifier_setup_is_compact(){let p=Params{n_parties:8,ell:30,beta:2,gamma:16,tau:3,salt_bytes:32};let s=Setup::verifier(p);assert_eq!(s.params.n(),1<<30);assert!(s.layout.is_pad.is_empty()&&s.layout.owned.is_empty());assert!(s.layout.pad.len()<1024);assert_eq!(s.layout.masks.iter().map(Vec::len).sum::<usize>(),256);}
 #[test]fn compact_setup_matches_full(){for ell in [12,14]{let params=Params{n_parties:8,ell,beta:2,gamma:16,tau:3,salt_bytes:32};let a=Setup::new(params.clone());let b=Setup::verifier(params);assert!(b.layout.owned.is_empty()&&b.layout.is_pad.is_empty());assert_eq!(a.layout.pad,b.layout.pad);assert_eq!(a.layout.masks.iter().flatten().map(|m|(m.y,m.x,m.h)).collect::<Vec<_>>(),b.layout.masks.iter().flatten().map(|m|(m.y,m.x,m.h)).collect::<Vec<_>>());let tail=vec![from_words([19,3]);8];assert_eq!(a.row.encode(&tail),b.row.encode(&tail));for j in 0..ell-3{for q in [0,1,(1<<(ell+1-j))-1]{assert_eq!(a.row.twiddle(ell+2-j,q),b.row.twiddle(ell+2-j,q));}}}}
}
