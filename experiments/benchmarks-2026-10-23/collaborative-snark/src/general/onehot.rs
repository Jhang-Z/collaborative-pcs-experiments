//! Fixed binary sparse index; virtual lookup values reduce to one binary PCS opening.
use std::{cell::RefCell,collections::BTreeSet};
use crate::{field::{Field,L,basis,chi,eq_expand},fs::Transcript,merkle::Hash,
    params::{Params,ceil_log2},setup::{Setup,Witness,Instance},protocol,product_tree,sha_zk};
use binius_hash::Blake3HashSuite as H;
use super::{distributed::{Runtime,Vector,EqualityLookup,bounds,integer,label},sparse::{ColumnMap,grouped_weights}};
const ZERO:Hash=[0;32];
pub const ROLE:u64=0x4f4e45484f543035;
const PUBLIC_SEED:u64=0x696e646578303035;
fn bytes(v:&[L])->&[u8]{bytemuck::cast_slice(v)}
#[derive(Clone,Debug)]
pub struct Key {pub row_bits:usize,pub col_bits:usize,pub entry_bits:usize,pub block_bits:usize,pub counts:[usize;3],pub params:Params,pub root:Hash}
impl Key {
    pub fn blocks(&self)->usize{(self.row_bits+self.col_bits).div_ceil(self.block_bits)}
    pub fn selector_bits(&self)->usize{ceil_log2(self.blocks())}
    pub fn ell(n:usize,gamma:usize,e:usize,a:usize,b:usize)->usize{
        let k=n/4;let q=e+b+ceil_log2(a.div_ceil(b));
        let safe=ceil_log2(2*(gamma+2+256usize.div_ceil(k)))+1;
        safe.max(q.saturating_sub(8+k.ilog2() as usize)+2).max(ceil_log2(gamma+2)+1)
    }
    pub fn valid(&self)->bool{
        let p=&self.params;
        matches!(self.block_bits,3|5)&&self.row_bits>0&&self.row_bits<40&&self.col_bits>0&&self.col_bits<48&&
        (3..40).contains(&self.entry_bits)&&p.n_parties.is_power_of_two()&&(8..=256).contains(&p.n_parties)&&
        p.beta==2&&(8..=1<<20).contains(&p.gamma)&&p.tau>=3&&p.tau<ceil_log2(p.gamma+2)&&p.salt_bytes==32&&
        self.entry_bits>=p.n_parties.ilog2() as usize&&
        self.counts.iter().try_fold(0usize,|a,&b|a.checked_add(b)).is_some_and(|n|n<=1usize<<self.entry_bits)&&
        p.ell==Self::ell(p.n_parties,p.gamma,self.entry_bits,self.row_bits+self.col_bits,self.block_bits)&&p.ell<40
    }
    pub fn binding(&self)->Vec<u8>{let mut b=vec![];for x in [self.row_bits,self.col_bits,self.entry_bits,self.block_bits]{b.extend((x as u64).to_le_bytes());}
        for x in self.counts{b.extend((x as u64).to_le_bytes());}crate::indexed_codec::params(&mut b,&self.params);b.extend(self.root);b}
    fn mix(&self,i:usize,rho:[L;3])->L{let mut end=0;for (a,&n) in self.counts.iter().enumerate(){end+=n;if i<end{return rho[a];}}L::ZERO}
    fn mix_eval(&self,r:&[L],rho:[L;3])->L{
        fn prefix(n:usize,r:&[L])->L{if n==1<<r.len(){return L::ONE;}let(mut sum,mut eq)=(L::ZERO,L::ONE);
            for j in (0..r.len()).rev(){if n>>j&1==1{sum+=eq*(L::ONE+r[j]);eq*=r[j];}else{eq*=L::ONE+r[j];}}sum}
        let(mut n,mut old,mut value)=(0,L::ZERO,L::ZERO);for (a,&count)in self.counts.iter().enumerate(){n+=count;let next=prefix(n,r);value+=rho[a]*(next+old);old=next;}value
    }
    fn chunks(&self,row:&[L],col:&[L])->Vec<Vec<L>>{let mut p=row.to_vec();p.extend(col);p.resize(self.blocks()*self.block_bits,L::ZERO);p.chunks_exact(self.block_bits).map(|q|q.to_vec()).collect()}
    fn instance(&self,point:&[L],value:L)->Instance{
        assert_eq!(point.len(),self.entry_bits+self.block_bits+self.selector_bits());let lk=self.params.k().ilog2() as usize;
        let mut free=point.to_vec();free.resize(8+lk+self.params.ell-2,L::ZERO);
        let mut rb=vec![L::ONE];rb.extend_from_slice(&free[8+lk..]);rb.push(L::ONE);
        Instance{r_h:free[..8].to_vec(),r_a:free[8..8+lk].to_vec(),r_b:rb,s_x:value}
    }
}
pub struct Index {pub key:Key,setup:Setup,witness:Witness,prepared:RefCell<Option<protocol::Prepared>>,
    addresses:Vec<Vector>,rows:Vector,permutation:Vector,sorted_keys:Vector,output_len:usize}
impl Index {
    pub fn new(rt:&mut Runtime,row_bits:usize,col_bits:usize,entries:Vec<(usize,usize,usize)>,map:ColumnMap,gamma:usize,tau:usize,b:usize)->Self{
        assert!(matches!(b,3|5));let mut set=BTreeSet::new();for x in entries {assert!(x.0<3&&x.1<1<<row_bits&&x.2<1<<col_bits);if !set.insert(x){set.remove(&x);}}
        let entries:Vec<_>=set.into_iter().collect();let count=entries.len().max(rt.n).next_power_of_two();
        let e=count.ilog2() as usize;let mut counts=[0;3];for &(a,_,_)in &entries{counts[a]+=1;}
        let params=Params{n_parties:rt.n,ell:Key::ell(rt.n,gamma,e,row_bits+col_bits,b),beta:2,gamma,tau,salt_bytes:32};
        let mut key=Key{row_bits,col_bits,entry_bits:e,block_bits:b,counts,params,root:ZERO};assert!(key.valid());
        let setup=Setup::new(key.params.clone());let mut witness=Witness{table:vec![L::ZERO;setup.params.k()*setup.params.n()]};
        let (width,lk)=(1<<b,setup.params.k().ilog2() as usize);let mut channels=vec![vec![L::ZERO;count];key.blocks()];
        let mut rows=vec![L::ZERO;count];let mut logical=vec![0;count];
        for i in 0..count {let (_,row,col)=entries.get(i).copied().unwrap_or((0,0,0));rows[i]=label(row);
            if i<entries.len(){let slot=col>>map.physical_bits;let offset=col&((1<<map.physical_bits)-1);logical[i]=slot*map.logical_bits+map.inverse[&offset];}
            let address=(row as u128)|((col as u128)<<row_bits);
            for j in 0..key.blocks(){let u=((address>>(j*b))&((width-1) as u128)) as usize;channels[j][i]=label(u);
                let bit=i+count*(u+width*j);let h=bit&255;let y=(bit>>8)&(setup.params.k()-1);let x=(1<<(setup.params.ell-1))|1|((bit>>(8+lk))<<1);
                assert!(x<setup.params.n()&&!setup.layout.is_pad[x]);witness.table[y*setup.params.n()+x]+=basis(h);
            }
        }
        let mut order:Vec<_>=(0..count).collect();order.sort_unstable_by_key(|&i|(logical[i],i));let mut permutation=vec![L::ZERO;count];
        for (j,&i)in order.iter().enumerate(){permutation[i]=label(j);}
        let sorted_keys=rt.load(order.iter().map(|&i|label(logical[i])).collect());let permutation=rt.load(permutation);let rows=rt.load(rows);
        let addresses=channels.into_iter().map(|v|rt.load(v)).collect();
        let prepared=Self::prepare(&setup,&witness);key.root=prepared.root;
        Self{key,setup,witness,prepared:RefCell::new(Some(prepared)),addresses,rows,permutation,sorted_keys,output_len:map.slots*map.logical_bits}
    }
    fn prepare(setup:&Setup,witness:&Witness)->protocol::Prepared{
        use rand::SeedableRng;let mut rng=rand::rngs::StdRng::seed_from_u64(PUBLIC_SEED);
        protocol::prepare_random::<H>(setup,witness,&mut rng,ROLE)
    }
    /// Traced proofs require the cached index prepared before tracing starts.
    pub fn take_prepared(&self)->protocol::Prepared {self.prepared.borrow_mut().take().unwrap_or_else(||{assert!(!crate::execution_trace::recording(),"prepare a fresh public index before starting a new trace");Self::prepare(&self.setup,&self.witness)})}
    pub fn column_weights(&self,rt:&mut Runtime,row:&[L],rho:[L;3])->Vector {
        let rp=row.to_vec();let key=self.key.clone();let weights=rt.map_local(&[self.rows],move||{let table=EqualityLookup::new(&rp);let key=key.clone();move|i,v|key.mix(i,rho)*table.value(integer(v[0]))});
        grouped_weights(rt,weights,self.permutation,self.sorted_keys,self.output_len)
    }
}
pub struct Proof {pub rounds:Vec<Vec<L>>,pub endpoints:Vec<L>,pub reduction:Vec<[L;3]>,pub evaluation:L,pub opening:protocol::Proof}
impl Proof {pub fn encode(&self)->Vec<u8>{let mut b=vec![];for q in &self.rounds{b.extend(bytes(q));}b.extend(bytes(&self.endpoints));for q in &self.reduction{b.extend(bytes(q));}b.extend(bytes(&[self.evaluation]));let opening=sha_zk::encode_pcs(&self.opening);b.extend((opening.len() as u64).to_le_bytes());b.extend(opening);b}}
fn begin(k:&Key,row:&[L],col:&[L],rho:[L;3],v:L,tr:&mut Transcript<'_,H>){tr.absorb(b"binary onehot index v1",&k.binding());tr.absorb(b"onehot row",bytes(row));tr.absorb(b"onehot col",bytes(col));tr.absorb(b"onehot mix/value",bytes(&[rho[0],rho[1],rho[2],v]));}
fn weights(k:&Key,q:&[Vec<L>],lambda:&[L])->Vec<L>{let width=1<<k.block_bits;let mut w=vec![L::ZERO;width<<k.selector_bits()];for j in 0..k.blocks(){for(u,x)in eq_expand(&q[j]).into_iter().enumerate(){w[u+width*j]=lambda[j]*x;}}w}
fn weight_eval(k:&Key,q:&[Vec<L>],lambda:&[L],p:&[L])->L{(0..k.blocks()).map(|j|lambda[j]*chi(j,&p[k.block_bits..])*crate::spartan::eq_eval(&q[j],&p[..k.block_bits])).sum()}
pub fn prove(rt:&mut Runtime,index:&Index,prepared:protocol::Prepared,row:&[L],col:&[L],rho:[L;3],value:L,tr:&mut Transcript<'_,H>)->Proof{
    let k=&index.key;begin(k,row,col,rho,value,tr);let q=k.chunks(row,col);let count=1<<k.entry_bits;
    let mut f:Vec<_>=(0..=k.blocks()).map(|_|Vector{id:rt.id(),len:count}).collect();let out=f.clone();let addr=index.addresses.clone();let query=q.clone();let key=k.clone();
    rt.run_effect(move|w|{let (lo,hi)=bounds(count,w.n,w.rank);for (j,&a)in addr.iter().enumerate(){let table=eq_expand(&query[j]);w.put(out[j].id,w.arrays[&a.id].iter().map(|&v|table[integer(v)]).collect());}
        w.put(out.last().unwrap().id,(lo..hi).map(|i|key.mix(i,rho)).collect());vec![]});
    let mut local:Option<Vec<Vec<L>>>=None;let mut rounds=vec![];let mut z=vec![];let mut claim=value;
    for _ in 0..k.entry_bits {
        if local.is_none()&&f[0].len<=count/rt.n {let req=f.iter().flat_map(|&v|(0..v.len).map(move|j|(v,j))).collect::<Vec<_>>();let cells=rt.get_many(&req);local=Some(cells.chunks_exact(f[0].len).map(|v|v.to_vec()).collect());rt.release(&f);}
        let poly=if let Some(values)=&local {local_round(values)}else{rt.product_round(&f)};assert_eq!(poly[0]+poly[1],claim);
        let x=tr.round(&ZERO,bytes(&poly)).field();claim=product_tree::interpolate(&poly,x);rounds.push(poly);z.push(x);
        if let Some(values)=&mut local{for v in values{*v=crate::code::fold_coeffs(v,x);}}else{let old=f;f=rt.fold_many(&old,x,&old);}
    }
    let endpoints:Vec<L>=if let Some(values)=local{values[..k.blocks()].iter().map(|v|v[0]).collect()}else{let end=rt.get_many(&f[..k.blocks()].iter().map(|&v|(v,0)).collect::<Vec<_>>());rt.release(&f);end};
    assert_eq!(claim,k.mix_eval(&z,rho)*endpoints.iter().copied().product::<L>());
    let mut ch=tr.round(&ZERO,bytes(&endpoints));let lambda:Vec<_>=(0..k.blocks()).map(|_|ch.field()).collect();
    let (width,len)=(1<<k.block_bits,1<<(k.block_bits+k.selector_bits()));let addr=index.addresses.clone();let point=z.clone();
    let partials=rt.run(move|w|{let table=EqualityLookup::new(&point);let(lo,hi)=bounds(count,w.n,w.rank);let eq:Vec<_>=(lo..hi).map(|i|table.value(i)).collect();let mut hist=vec![L::ZERO;len];
        for(j,v)in addr.iter().enumerate(){for (i,&u)in w.arrays[&v.id].iter().enumerate(){hist[j*width+integer(u)]+=eq[i];}}hist});
    let mut hist=vec![L::ZERO;len];for h in partials{for(x,y)in hist.iter_mut().zip(h){*x+=y;}}
    let mut reduced=vec![hist,weights(k,&q,&lambda)];let mut claim: L=endpoints.iter().zip(&lambda).map(|(&a,&b)|a*b).sum();let mut p=vec![];let mut reduction=vec![];
    for _ in 0..k.block_bits+k.selector_bits(){let poly:[L;3]=local_round(&reduced).try_into().unwrap();assert_eq!(poly[0]+poly[1],claim);let x=tr.round(&ZERO,bytes(&poly)).field();claim=product_tree::interpolate(&poly,x);p.push(x);reduction.push(poly);for v in &mut reduced{*v=crate::code::fold_coeffs(v,x);}}
    let evaluation=reduced[0][0];assert_eq!(claim,evaluation*weight_eval(k,&q,&lambda,&p));z.extend(p);let inst=k.instance(&z,evaluation);
    tr.absorb(b"onehot index instance",&inst.to_bytes());let(opening,_,_)=protocol::open_prepared_in::<H>(&index.setup,&inst,prepared,tr);tr.absorb(b"onehot index opening",&sha_zk::encode_pcs(&opening));
    Proof{rounds,endpoints,reduction,evaluation,opening}
}
fn local_round(f:&[Vec<L>])->Vec<L>{let points:Vec<_>=(0..=f.len()).map(product_tree::point).collect();let mut q=vec![L::ZERO;points.len()];for i in 0..f[0].len()/2{for(t,&x)in points.iter().enumerate(){q[t]+=f.iter().map(|v|v[2*i]+x*(v[2*i]+v[2*i+1])).product::<L>();}}q}
pub fn verify(k:&Key,row:&[L],col:&[L],rho:[L;3],value:L,p:&Proof,tr:&mut Transcript<'_,H>)->Result<(),String>{
    if !k.valid()||row.len()!=k.row_bits||col.len()!=k.col_bits||p.rounds.len()!=k.entry_bits||p.endpoints.len()!=k.blocks()||p.reduction.len()!=k.block_bits+k.selector_bits()||p.opening.roots.first()!=Some(&k.root){return Err("onehot shape/root".into());}
    begin(k,row,col,rho,value,tr);let mut claim=value;let mut z=vec![];
    for poly in &p.rounds{if poly.len()!=k.blocks()+2||poly[0]+poly[1]!=claim{return Err("onehot sumcheck".into());}let x=tr.round(&ZERO,bytes(poly)).field();claim=product_tree::interpolate(poly,x);z.push(x);}
    if claim!=k.mix_eval(&z,rho)*p.endpoints.iter().copied().product::<L>(){return Err("onehot endpoint".into());}
    let mut ch=tr.round(&ZERO,bytes(&p.endpoints));let lambda:Vec<_>=(0..k.blocks()).map(|_|ch.field()).collect();let q=k.chunks(row,col);
    claim=p.endpoints.iter().zip(&lambda).map(|(&a,&b)|a*b).sum();let mut point=vec![];
    for poly in &p.reduction{if poly[0]+poly[1]!=claim{return Err("onehot reduction".into());}let x=tr.round(&ZERO,bytes(poly)).field();claim=product_tree::interpolate(poly,x);point.push(x);}
    if claim!=p.evaluation*weight_eval(k,&q,&lambda,&point){return Err("onehot reduced endpoint".into());}
    z.extend(point);let inst=k.instance(&z,p.evaluation);tr.absorb(b"onehot index instance",&inst.to_bytes());
    protocol::verify_in::<H>(&Setup::verifier_compact(k.params.clone()),&inst,&p.opening,tr,ROLE)?;
    tr.absorb(b"onehot index opening",&sha_zk::encode_pcs(&p.opening));Ok(())
}

#[cfg(test)]mod tests{
    use super::*;
    use crate::{field::Random,merkle::Hasher,params::Layout};
    use rand::{SeedableRng,rngs::StdRng};
    #[test]fn cube_never_intersects_padding_or_tensor_masks(){
        for n in [8,16,32,64,128,256]{for gamma in [16,520,871]{for b in [3,5]{
            let p=Params{n_parties:n,ell:Key::ell(n,gamma,17,36,b),beta:2,gamma,tau:3,salt_bytes:32};
            let layout=Layout::verifier(&p);let in_cube=|x:usize|x&1==1&&x>>(p.ell-1)==1;
            assert!(layout.pad.iter().all(|&x|!in_cube(x)));
            assert!(layout.masks.iter().flatten().all(|m|!in_cube(m.x)));
        }}}
    }
    #[test]fn onehot_matches_direct_sparse_evaluation_and_rejects_mutations(){
        let mut rng=StdRng::seed_from_u64(903);let hasher=Hasher::<H>::default();
        for b in [3,5]{
            let mut rt=Runtime::new(8);let entries:Vec<_>=(0..23).map(|i|(i%3,i%8,(i*7)%16)).collect();
            let map=ColumnMap::new(3,2,&(0..8).collect::<Vec<_>>());
            let index=Index::new(&mut rt,3,4,entries.clone(),map,16,3,b);rt.flush();
            let row:Vec<_>=(0..3).map(|_|L::random(&mut rng)).collect();let col:Vec<_>=(0..4).map(|_|L::random(&mut rng)).collect();let rho=std::array::from_fn(|_|L::random(&mut rng));
            let value=entries.iter().map(|&(a,r,c)|rho[a]*chi(r,&row)*chi(c,&col)).sum();
            let mut tr=Transcript::new_global(&hasher,b"onehot-test");
            let mut p=prove(&mut rt,&index,index.take_prepared(),&row,&col,rho,value,&mut tr);
            let check=|p:&Proof,k:&Key,v:L|{let mut tr=Transcript::new_global(&hasher,b"onehot-test");verify(k,&row,&col,rho,v,p,&mut tr)};
            check(&p,&index.key,value).unwrap();assert!(check(&p,&index.key,value+L::ONE).is_err());
            p.rounds[0][0]+=L::ONE;assert!(check(&p,&index.key,value).is_err());p.rounds[0][0]+=L::ONE;
            p.endpoints[0]+=L::ONE;assert!(check(&p,&index.key,value).is_err());p.endpoints[0]+=L::ONE;
            p.reduction[0][0]+=L::ONE;assert!(check(&p,&index.key,value).is_err());p.reduction[0][0]+=L::ONE;
            p.evaluation+=L::ONE;assert!(check(&p,&index.key,value).is_err());p.evaluation+=L::ONE;
            let mut k=index.key.clone();k.root[0]^=1;assert!(check(&p,&k,value).is_err());
            let mut k=index.key.clone();k.counts[0]+=1;assert!(check(&p,&k,value).is_err());
            p.opening.openings[0][0].values[0]+=L::ONE;assert!(check(&p,&index.key,value).is_err());
        }
    }
}
