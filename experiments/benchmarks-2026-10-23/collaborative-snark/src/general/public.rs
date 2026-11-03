//! Distributed equivalents of the existing public arithmetic and hash proofs.
//! All table cells live in Runtime owners; final proofs use the unchanged verifier.
use crate::{field::{Field,L},fs::Transcript,merkle::{Hash,Hasher},
    public_pcs,product_tree,spartan::eq_eval};
use binius_hash::Blake3HashSuite as H;
use super::distributed::{Runtime,Vector};
const ZERO:Hash=[0;32];
fn bytes(x:&[L])->&[u8]{bytemuck::cast_slice(x)}
fn raw(x:L)->Hash {bytemuck::cast(x)}
fn field(x:Hash)->L {bytemuck::cast(x)}

pub struct Merkle {levels:Vec<Vector>,root:Hash}
impl Merkle {
    fn new(rt:&mut Runtime,cw:Vector,layer:usize)->Self {
        let local=if cw.len>=rt.n {(cw.len/rt.n).ilog2() as usize}else{0};
        let node=move|depth:usize,i:usize,a:L,b:L|{let h=Hasher::<H>::scoped(3).at_layer(layer as u64);
            field(if depth==0 {h.leaf(layer as u64,i as u64,bytes(&[a,b]),&[])}else{h.node(&raw(a),&raw(b))})};
        let mut levels=rt.pair_layers(cw,local,node);
        let mut current=levels.last().copied().unwrap_or(cw);
        while current.len>1 {let depth=levels.len();current=rt.pairs(current,move|i,a,b|node(depth,i,a,b));levels.push(current);}
        let root=raw(rt.small(current)[0]);Self{levels,root}
    }
}

pub struct Committed {pub key:public_pcs::Key,pub values:Vector,cw:Vector,tree:Merkle}
pub fn commit(rt:&mut Runtime,values:Vector,queries:usize)->Committed {
    assert!(values.len.is_power_of_two()&&values.len>=16);
    let cw=rt.encode(values);let tree=Merkle::new(rt,cw,0);
    let key=public_pcs::Key{log:values.len.ilog2() as usize,queries,root:tree.root};Committed{key,values,cw,tree}
}
pub fn open_batch(rt:&mut Runtime,c:&Committed,points:&[Vec<L>],values:&[L],tr:&mut Transcript<'_,H>)->public_pcs::Proof {
    tr.absorb(b"public batch opening key",&c.key.binding());tr.absorb(b"public batch count",&(points.len() as u64).to_le_bytes());
    for(p,&v)in points.iter().zip(values){tr.absorb(b"public batch point",bytes(p));tr.absorb(b"public batch value",bytes(&[v]));}
    let mut ch=tr.round(&ZERO,b"public batch coefficients");let a:Vec<_>=(0..points.len()).map(|_|ch.field()).collect();
    let mut s:L=a.iter().zip(values).map(|(&a,&v)|a*v).sum();
    let mut w=rt.equality_sum(c.values.len,points,&a);
    let folds=c.key.log-3;let(mut f,mut cw)=(c.values,c.cw);
    let(mut roots,mut rounds,mut trees,mut words)=(vec![c.key.root],vec![],vec![],vec![]);
    let tail_cells=4096.max(6*c.values.len/rt.n);
    for j in 0..folds {
        if 6*f.len<=tail_cells {break;}
        let ab=rt.pair_reduce(&[f,w],2,|x,out|{out[0]+=x[0][0]*x[1][0];out[1]+=(x[0][1]+x[0][0])*(x[1][1]+x[1][0]);});let(a,b)=(ab[0],ab[1]);
        rounds.push((a,b));let r=tr.round(&roots[j],bytes(&[a,b])).field();assert_ne!(r,L::ONE);
        s=a+(s+b)*r+b*r*r;
        let mut release=vec![w];if f.id!=c.values.id {release.push(f);}
        words.push(cw);[f,w,cw]=rt.fold_public(f,w,cw,r,c.key.log,&release);
        if j+1<folds {let t=Merkle::new(rt,cw,j+1);roots.push(t.root);trees.push(t);}
    }
    let cut=rounds.len();
    assert!(6*f.len<=tail_cells);
    let gathered=rt.get_many(&[f,w,cw].into_iter().flat_map(|v|(0..v.len).map(move|j|(v,j))).collect::<Vec<_>>());
    let (mut lf,mut lw,mut lcw)=(gathered[..f.len].to_vec(),gathered[f.len..2*f.len].to_vec(),gathered[2*f.len..].to_vec());
    let mut release=vec![w];if f.id!=c.values.id {release.push(f);}if cw.id!=c.cw.id {release.push(cw);}rt.release(&release);
    let code=crate::code::RowCode::compact(c.key.log,2);
    let(mut local_words,mut local_trees)=(vec![],vec![]);
    for j in cut..folds {
        let h=Hasher::<H>::scoped(3).at_layer(j as u64);
        let tree=crate::merkle::Tree::build(&h,lcw.chunks_exact(2).enumerate().map(|(i,p)|h.leaf(j as u64,i as u64,bytes(p),&[])).collect());
        if j==cut {assert_eq!(tree.root(),roots[j]);}else{roots.push(tree.root());}
        let(mut a,mut b)=(L::ZERO,L::ZERO);
        for(x,y)in lf.chunks_exact(2).zip(lw.chunks_exact(2)){a+=x[0]*y[0];b+=(x[1]+x[0])*(y[1]+y[0]);}
        rounds.push((a,b));let r=tr.round(&roots[j],bytes(&[a,b])).field();assert_ne!(r,L::ONE);
        s=a+(s+b)*r+b*r*r;
        lf=crate::code::fold_coeffs(&lf,r);lw=crate::code::fold_coeffs(&lw,r);
        let next=code.fold(&lcw,r);local_words.push(std::mem::replace(&mut lcw,next));local_trees.push(tree);
    }
    let tail=lf;assert_eq!(s,tail.iter().zip(lw).map(|(&x,y)|x*y).sum::<L>());
    let mut ch=tr.round(&ZERO,bytes(&tail));let queries:Vec<_>=(0..c.key.queries).map(|_|ch.bits((c.key.log+1) as u32) as usize).collect();
    let mut requests=vec![];
    for j in 0..cut {let tree=if j==0 {&c.tree}else{&trees[j-1]};
        for &q in &queries {let target=q>>j;requests.extend([(words[j],2*target),(words[j],2*target+1)]);
            for(depth,&v)in tree.levels[..tree.levels.len()-1].iter().enumerate(){requests.push((v,(target>>depth)^1));}
        }
    }
    let responses=rt.get_many(&requests);
    let mut released=words.iter().skip(1).copied().collect::<Vec<_>>();for tree in &trees {released.extend(&tree.levels);}rt.release(&released);
    let mut cursor=0;let mut openings=vec![vec![];queries.len()];
    for j in 0..cut {let tree=if j==0 {&c.tree}else{&trees[j-1]};let depth=tree.levels.len()-1;
        for opening in &mut openings {let pair=[responses[cursor],responses[cursor+1]];cursor+=2;
            let path=responses[cursor..cursor+depth].iter().map(|&x|raw(x)).collect();cursor+=depth;
            opening.push(public_pcs::Query{pair,path});
        }
    }assert_eq!(cursor,responses.len());
    for j in cut..folds {for(opening,&q)in openings.iter_mut().zip(&queries){let i=q>>j;
        opening.push(public_pcs::Query{pair:[local_words[j-cut][2*i],local_words[j-cut][2*i+1]],path:local_trees[j-cut].path(i)});
    }}
    let proof=public_pcs::Proof{roots,rounds,tail,openings};tr.absorb(b"public-index opening",&proof.encode());proof
}
// Collect at most one owner's original share (or the small constant floor).
// This changes only scheduling; the product-tree proof and challenges are identical.
pub const PRODUCT_BOUNDARY_CELLS:usize=4096;
pub struct ProductTree {levels:Vec<Vector>,upper:Vec<Vec<L>>,pub roots:[L;8]}
impl ProductTree {
    pub fn new(rt:&mut Runtime,leaves:Vector,depth:usize)->Self {
        assert_eq!(leaves.len,8<<depth);
        let boundary_limit=PRODUCT_BOUNDARY_CELLS.max(leaves.len/rt.n);
        let cut=leaves.len.ilog2().saturating_sub(boundary_limit.ilog2()) as usize;
        let local=cut.min(if leaves.len>=rt.n {(leaves.len/rt.n).ilog2() as usize}else{0});
        let mut levels=vec![leaves];levels.extend(rt.pair_layers(leaves,local,|_,_,a,b|a*b));
        for _ in local..cut {levels.push(rt.pairs(*levels.last().unwrap(),|_,a,b|a*b));}
        let boundary=*levels.last().unwrap();
        let mut upper=vec![rt.get_many(&(0..boundary.len).map(|j|(boundary,j)).collect::<Vec<_>>())];
        for _ in cut..depth {let next=upper.last().unwrap().chunks_exact(2).map(|v|v[0]*v[1]).collect();upper.push(next);}
        let roots=upper.last().unwrap().as_slice().try_into().unwrap();Self{levels,upper,roots}
    }
}
pub fn product_prove(rt:&mut Runtime,tree:ProductTree,tr:&mut Transcript<'_,H>)->(product_tree::Proof,Vec<L>,L) {
    let mut ch=tr.round(&ZERO,bytes(&tree.roots));let mut r:Vec<_>=(0..3).map(|_|ch.field()).collect();
    let mut claim=public_pcs::evaluate(&tree.roots,&r);let mut layers=vec![];
    // Public tails only. Bound controller work by one owner's original share;
    // retrieval and subsequent arithmetic remain inside the online trace.
    let cut=tree.levels.len()-1;let depth=cut+tree.upper.len()-1;
    for level in (0..depth).rev() {
        let tail_cells=if level<cut {1024.max(3*tree.levels[level].len/2/rt.n)}else{1024};
        let(mut f,mut local)=if level>=cut {
            let v=&tree.upper[level-cut];
            (vec![],Some(vec![v.chunks_exact(2).map(|p|p[0]).collect::<Vec<_>>(),v.chunks_exact(2).map(|p|p[1]).collect(),crate::field::eq_expand(&r)]))
        }else{
            let v=tree.levels[level];let a=rt.pairs(v,|_,a,_|a);let b=rt.pairs(v,|_,_,b|b);
            let e=rt.equality_sum(a.len,&[r.clone()],&[L::ONE]);(vec![a,b,e],None)
        };
        let mut rounds=vec![];let mut next=vec![];
        for _ in 0..r.len() {
            if local.is_none()&&3*f[0].len<=tail_cells {
                let requests=f.iter().flat_map(|&v|(0..v.len).map(move|j|(v,j))).collect::<Vec<_>>();
                let values=rt.get_many(&requests);let len=f[0].len;
                local=Some(values.chunks_exact(len).map(|v|v.to_vec()).collect());rt.release(&f);
            }
            let q:[L;4]=if let Some(values)=&local {
                let mut q=[L::ZERO;4];
                for i in 0..values[0].len()/2 {for (j,y) in q.iter_mut().enumerate() {
                    let x=product_tree::point(j);*y+=values.iter().map(|v|v[2*i]+x*(v[2*i]+v[2*i+1])).product::<L>();
                }}q
            }else{rt.product_round(&f).try_into().unwrap()};assert_eq!(q[0]+q[1],claim);
            let x=tr.round(&ZERO,bytes(&q)).field();claim=product_tree::interpolate(&q,x);next.push(x);rounds.push(q);
            if let Some(values)=&mut local {for v in values {*v=crate::code::fold_coeffs(v,x);}}
            else{let old=f;f=rt.fold_many(&old,x,&old);}
        }
        let endpoints:[L;2]=if let Some(values)=local {[values[0][0],values[1][0]]}
            else{let e=rt.get_many(&[(f[0],0),(f[1],0)]).try_into().unwrap();rt.release(&f);e};
        assert_eq!(claim,endpoints[0]*endpoints[1]*eq_eval(&r,&next));
        let x=tr.round(&ZERO,bytes(&endpoints)).field();claim=endpoints[0]+x*(endpoints[0]+endpoints[1]);r=vec![x];r.extend(next);
        layers.push(product_tree::Layer{rounds,endpoints});
    }
    (product_tree::Proof{roots:tree.roots,layers},r,claim)
}
#[cfg(test)]mod tests {
    use super::*;use super::super::distributed::label;
    #[test]fn local_merkle_levels_share_one_owner_command() {
        let mut rt=Runtime::new(8);let input=rt.generate(64,label);rt.flush();
        let before=rt.command_count();let _=Merkle::new(&mut rt,input,0);
        assert!(rt.command_count()-before<=5*8,"local tree levels were dispatched separately");
    }
    #[test]fn bounded_upper_tree_uses_one_collection() {
        let mut rt=Runtime::new(16);let values=rt.generate(PRODUCT_BOUNDARY_CELLS,label);rt.seal();rt.flush();
        let before=rt.command_count();let tree=ProductTree::new(&mut rt,values,9);
        assert_eq!(rt.command_count()-before,16);
        let before=rt.command_count();let h=Hasher::<H>::default();
        let(p,r,v)=product_prove(&mut rt,tree,&mut Transcript::new_global(&h,b"upper"));
        assert_eq!(rt.command_count(),before,"upper proof redispatched to workers");
        assert_eq!(product_tree::verify(&p,9,&mut Transcript::new_global(&h,b"upper")).unwrap(),(r,v));
    }
    #[test]fn bounded_product_tails_preserve_full_transcript() {
        let h=Hasher::<H>::default();
        for depth in [0,1,6,8,10,14] {
            let values=(0..8<<depth).map(|i|label(i+3)).collect::<Vec<_>>();
            let expected=product_tree::prove(product_tree::Tree::new(values.clone(),depth),&mut Transcript::new_global(&h,b"tail"));
            let mut rt=Runtime::new(8);let input=rt.load(values);rt.seal();
            let tree=ProductTree::new(&mut rt,input,depth);
            let actual=product_prove(&mut rt,tree,&mut Transcript::new_global(&h,b"tail"));
            assert_eq!(actual.0.encode(),expected.0.encode());assert_eq!((actual.1,actual.2),(expected.1,expected.2));
        }
    }
    #[test]fn adaptive_product_tails_reduce_distributed_rounds() {
        let mut rt=Runtime::new(8);let values=rt.generate(8<<14,|i|label(i+3));rt.seal();
        let tree=ProductTree::new(&mut rt,values,14);assert_eq!(tree.levels.len()-1,3);
        let before=rt.command_count();let h=Hasher::<H>::default();
        let(p,r,v)=product_prove(&mut rt,tree,&mut Transcript::new_global(&h,b"adaptive"));
        // Three distributed levels: three setup commands, three two-command
        // rounds, one gather and one release per owner. All later rounds local.
        assert_eq!(rt.command_count()-before,3*11*8);
        assert_eq!(product_tree::verify(&p,14,&mut Transcript::new_global(&h,b"adaptive")).unwrap(),(r,v));
    }
    #[test]fn public_local_suffix_preserves_reusable_commitment_and_proof() {
        let h=Hasher::<H>::default();
        for (log,n) in [(4,8),(8,16),(12,8),(16,16)] {
            let values:Vec<_>=(0..1<<log).map(|i|label(i+13)).collect();
            let reference=public_pcs::commit(values.clone(),16);
            let mut rt=Runtime::new(n);let source=rt.load(values.clone());rt.seal();let c=commit(&mut rt,source,16);
            for offset in [1,7] {
                let points:Vec<Vec<L>>=(0..2).map(|j|(0..log).map(|i|label(offset+i+j)).collect()).collect();
                let claims:Vec<_>=points.iter().map(|p|public_pcs::evaluate(&values,p)).collect();
                let actual=open_batch(&mut rt,&c,&points,&claims,&mut Transcript::new_global(&h,b"suffix"));
                let expected=public_pcs::open_batch(&reference,&points,&claims,&mut Transcript::new_global(&h,b"suffix"));
                assert_eq!(actual.encode(),expected.encode());
                public_pcs::verify_batch(&c.key,&points,&claims,&actual,&mut Transcript::new_global(&h,b"suffix")).unwrap();
                let mut bad=actual.clone();bad.openings[0].last_mut().unwrap().pair[0]+=L::ONE;
                assert!(public_pcs::verify_batch(&c.key,&points,&claims,&bad,&mut Transcript::new_global(&h,b"suffix")).is_err());
            }
        }
    }
    #[test]fn public_proofs_match_existing_verifiers() {
        let mut rt=Runtime::new(8);let values:Vec<_>=(0..64).map(|i|label(i+7)).collect();let source=rt.load(values.clone());rt.seal();
        let c=commit(&mut rt,source,64);let reference=public_pcs::commit(values.clone(),64);assert_eq!(c.key.root,reference.key.root);
        let point=vec![label(3);6];let value=public_pcs::evaluate(&values,&point);let h=Hasher::<H>::default();
        let p=open_batch(&mut rt,&c,&[point.clone()],&[value],&mut Transcript::new_global(&h,b"peer public"));
        let expected=public_pcs::open_batch(&reference,&[point.clone()],&[value],&mut Transcript::new_global(&h,b"peer public"));
        assert_eq!(p.encode(),expected.encode());public_pcs::verify(&c.key,&point,value,&p,&mut Transcript::new_global(&h,b"peer public")).unwrap();
        let input=rt.generate(8<<4,|i|label(i+1));let tree=ProductTree::new(&mut rt,input,4);
        let(p,r,s)=product_prove(&mut rt,tree,&mut Transcript::new_global(&h,b"peer product"));
        let (rr,ss)=product_tree::verify(&p,4,&mut Transcript::new_global(&h,b"peer product")).unwrap();assert_eq!((r,s),(rr,ss));
    }
}
