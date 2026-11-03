//! Distributed compact public sparse authentication; the core compact verifier is reused.
use std::{collections::{BTreeMap,HashMap},sync::Arc};
use crate::{field::{Field,L},fs::Transcript,merkle::Hash,product_tree,compact_sparse_matrix as sparse_matrix};
use binius_hash::Blake3HashSuite as H;
use super::{distributed::{Runtime,Vector,EqualityLookup,integer,label},public::{self,Committed,ProductTree}};
const ZERO:Hash=[0;32];fn bytes(x:&[L])->&[u8]{bytemuck::cast_slice(x)}

#[derive(Clone)]
pub struct ColumnMap {pub physical_bits:usize,pub logical_bits:usize,pub slots:usize,pub inverse:Arc<HashMap<usize,usize>>}
impl ColumnMap {pub fn new(physical_bits:usize,slots:usize,map:&[usize])->Self{Self{physical_bits,logical_bits:map.len(),slots,inverse:Arc::new(map.iter().enumerate().map(|(j,&p)|(p,j)).collect())}}}

pub struct Index {pub key:sparse_matrix::Key,committed:Committed,final_committed:Committed,channels:Vec<Vector>,final_channels:Vec<Vector>,permutation:Vector,sorted_keys:Vector,output_len:usize}
impl Index {
    #[cfg(test)] pub fn from_data(rt:&mut Runtime,data:sparse_matrix::IndexData)->Self {Self::from_data_mapped(rt,data,None)}
    pub fn from_data_mapped(rt:&mut Runtime,data:sparse_matrix::IndexData,mapping:Option<ColumnMap>)->Self {
        let(row_bits,col_bits,queries,count,counts,values,finals)=data.into_tables();assert!(count>=rt.n);
        // Circuit addresses and the packing map are fixed public index data.
        // Cache their stable sort once; challenge-dependent weights stay online.
        let output_len=mapping.as_ref().map_or(1<<col_bits,|m|m.slots*m.logical_bits);
        let used:usize=counts.iter().sum();
        let keys=(0..count).map(|i|{
            let col=integer(values[2*count+i])|(integer(values[3*count+i])<<(col_bits/2));
            if let Some(m)=&mapping {let slot=col>>m.physical_bits;let p=col&((1<<m.physical_bits)-1);
                let logical=m.inverse.get(&p).copied().unwrap_or_else(||{assert!(i>=used,"real column absent from packing map");0});
                slot*m.logical_bits+logical
            }else{col}
        }).collect::<Vec<_>>();
        assert!(keys.iter().all(|&j|j<output_len));
        let mut order=(0..count).collect::<Vec<_>>();order.sort_unstable_by_key(|&i|(keys[i],i));
        let mut positions=vec![L::ZERO;count];for (position,&i) in order.iter().enumerate(){positions[i]=label(position);}
        let sorted_keys=rt.load(order.iter().map(|&i|label(keys[i])).collect());let permutation=rt.load(positions);
        let values=rt.load(values);let finals=rt.load(finals);
        let committed=public::commit(rt,values,queries);let final_committed=public::commit(rt,finals,queries);
        let key=sparse_matrix::Key{row_bits,col_bits,entry_bits:count.ilog2() as usize,channel_bits:3,counts,pcs:committed.key.clone(),final_pcs:final_committed.key.clone()};
        let b=1<<key.table_bits();let channels=(0..8).map(|c|rt.slice(values,c*count,count)).collect();
        let final_channels=(0..4).map(|c|rt.slice(finals,c*b,b)).collect();
        Self{key,committed,final_committed,channels,final_channels,permutation,sorted_keys,output_len}
    }
    pub fn column_weights(&self,rt:&mut Runtime,row:&[L],rho:[L;3])->Vector {
        let output_len=self.output_len;
        let chunks=self.key.chunks();let rp=row.to_vec();let key=self.key.clone();
        let weights=rt.map_local(&[self.channels[0],self.channels[1]],move|| {
            let a=EqualityLookup::new(&rp[..chunks[0]]);let b=EqualityLookup::new(&rp[chunks[0]..]);
            {let key=key.clone();move|i,v|a.value(integer(v[0]))*b.value(integer(v[1]))*key.mix(i,rho)}
        });
        grouped_weights(rt,weights,self.permutation,self.sorted_keys,output_len)
    }
}
pub(super) fn grouped_weights(rt:&mut Runtime,weights:Vector,permutation:Vector,sorted_keys:Vector,output_len:usize)->Vector {
    let count=weights.len;
        let sorted_weights=Vector{id:rt.id(),len:count};
        rt.run_effect(move|w| {
            let records=w.arrays[&weights.id].iter().zip(&w.arrays[&permutation.id]).map(|(&x,&p)|(integer(p),x)).collect();
            w.route_dense(sorted_weights.id,count,records,count);w.remove(weights.id);vec![]
        });
        // Reduce sorted runs locally. Only <=2N boundary summaries reach the controller.
        let grouped=rt.id();let summaries=rt.run(move|w| {
            let mut groups:Vec<L>=vec![];
            for (&key,&value) in w.arrays[&sorted_keys.id].iter().zip(&w.arrays[&sorted_weights.id]) {
                if groups.len()>=2&&groups[groups.len()-2]==key {let last=groups.len()-1;groups[last]+=value;}
                else{groups.extend([key,value]);}
            }
            let response=if groups.is_empty(){vec![L::ZERO;5]}else{
                vec![label(groups.len()/2),groups[0],groups[1],groups[groups.len()-2],groups[groups.len()-1]]};
            w.put(grouped,groups);response
        });
        let mut boundary:BTreeMap<usize,(L,usize)>=BTreeMap::new();
        for (rank,s) in summaries.iter().enumerate() {let count=integer(s[0]);if count>0 {
            for (key,value) in std::iter::once((integer(s[1]),s[2])).chain(if count>1 {Some((integer(s[3]),s[4]))}else{None}) {
                let e=boundary.entry(key).or_insert((L::ZERO,rank));e.0+=value;e.1=rank;
            }
        }}
        let mut corrections=vec![vec![];rt.n];for(key,(value,rank))in boundary {corrections[rank].push((key,value));}
        let payloads=corrections.into_iter().map(|entries|{let mut b=vec![];for(key,value)in entries{b.extend((key as u64).to_le_bytes());b.extend(bytemuck::bytes_of(&value));}b}).collect();
        let out=Vector{id:rt.id(),len:output_len};
        rt.run_packets_effect(payloads,move|w,packet| {
            let a=&w.arrays[&grouped];let mut entries=vec![];
            if a.len()>4 {for p in a[2..a.len()-2].chunks_exact(2) {entries.push((integer(p[0]),p[1]));}}
            entries.extend(packet.chunks_exact(40).map(|p|(u64::from_le_bytes(p[..8].try_into().unwrap()) as usize,bytemuck::pod_read_unaligned(&p[8..]))));w.route(out.id,out.len,entries,false);w.remove(grouped);vec![]
        });rt.release(&[sorted_weights]);out
}

fn endpoints(rt:&mut Runtime,index:&Index,aux:&[Vector],r:&[L])->Vec<L> {
    rt.evaluate_batch(&index.channels.iter().chain(aux).copied().collect::<Vec<_>>(),r)
}
pub fn prove(rt:&mut Runtime,index:&Index,row:&[L],col:&[L],rho:[L;3],value:L,tr:&mut Transcript<'_,H>)->sparse_matrix::Proof {
    let k=&index.key;assert_eq!((row.len(),col.len()),(k.row_bits,k.col_bits));sparse_matrix::begin(k,row,col,rho,value,tr);
    let queries=[row[..k.row_bits/2].to_vec(),row[k.row_bits/2..].to_vec(),col[..k.col_bits/2].to_vec(),col[k.col_bits/2..].to_vec()];
    let aux_channels:Vec<_>=(0..4).map(|c|rt.equality_lookup(index.channels[c],&queries[c])).collect();
    let aux_values=rt.concat(&aux_channels);let aux=public::commit(rt,aux_values,k.pcs.queries);tr.absorb(b"memory read values",&aux.key.binding());
    let key=k.clone();let mix=rt.map(&[index.channels[0]],move|i,_|key.mix(i,rho));
    let mut f=aux_channels.clone();f.push(mix);let(mut rounds,mut r,mut claim)=(vec![],vec![],value);
    for _ in 0..k.entry_bits {
        let q=rt.product_round(&f);assert_eq!(q[0]+q[1],claim);let x=tr.round(&ZERO,bytes(&q)).field();claim=product_tree::interpolate(&q,x);r.push(x);rounds.push(q);
        let old=f;let release=old.iter().copied().filter(|v|!aux_channels.iter().any(|a|a.id==v.id)).collect::<Vec<_>>();
        f=rt.fold_many(&old,x,&release);
    }
    let end=endpoints(rt,index,&aux_channels,&r);
    assert_eq!(claim,(0..4).map(|c|end[8+c]).product::<L>()*k.mix_eval(&r,rho));
    let (ic1,ac1)=sparse_matrix::claims(&r,&end,tr);rt.release(&f);
    let mut ch=tr.round(&ZERO,b"memory tuple compression");let hash:[L;3]=std::array::from_fn(|_|ch.field());
    let mut read_channels=vec![];let mut table_channels=vec![];
    for c in 0..4 {let query=rt.equality_sum(index.final_channels[c].len,&[queries[c].clone()],&[L::ONE]);for h in 0..2 {
        read_channels.push(rt.map(&[aux_channels[c],index.channels[4+c],index.channels[c]],move|_,v|L::ONE+hash[0]*v[0]+hash[1]*(if h==0{L::ONE}else{sparse_matrix::time_step()})*v[1]+hash[2]*v[2]));
        table_channels.push(rt.map(&[index.final_channels[c],query],move|j,v| {
            L::ONE+hash[0]*v[1]+hash[2]*label(j)+if h==1{hash[1]*v[0]}else{hash[1]}
        }));
    }rt.release(&[query]);}
    let width=1<<(k.product_bits()-1);let values=Vector{id:rt.id(),len:16*width};
    let sources=read_channels.iter().copied().enumerate().flat_map(|(channel,v)|[(v,2*channel*width),(table_channels[channel^1],(2*channel+1)*width)]).collect::<Vec<_>>();
    rt.run_effect(move|w| {
        let mut records=vec![];
        for &(v,offset) in &sources {let(lo,_)=super::distributed::bounds(v.len,w.n,w.rank);
            records.extend(w.arrays[&v.id].iter().enumerate().map(|(j,&x)|(offset+lo+j,x+L::ONE)));
        }
        // Missing positions are multiplicative identities; send only actual cells.
        w.route(values.id,values.len,records,false);
        for x in w.arrays.get_mut(&values.id).unwrap(){*x+=L::ONE;}vec![]
    });rt.release(&read_channels);rt.release(&table_channels);
    let products=ProductTree::new(rt,values,k.product_bits());
    sparse_matrix::bind_products(&products.roots,tr).unwrap();let(products,rr,rv)=public::product_prove(rt,products,tr);
    let memory_endpoints=endpoints(rt,index,&aux_channels,&rr[..k.entry_bits]);
    let final_endpoints=rt.evaluate_batch(&index.final_channels,&rr[..k.table_bits()]).try_into().unwrap();
    assert_eq!(rv,sparse_matrix::product_leaf(k,[&queries[0],&queries[1],&queries[2],&queries[3]],&memory_endpoints,&final_endpoints,&rr,hash));
    let(ic2,ac2)=sparse_matrix::claims(&rr[..k.entry_bits],&memory_endpoints,tr);
    let(fc,fv)=sparse_matrix::final_claim(&rr[..k.table_bits()],&final_endpoints,tr);
    let opening=public::open_batch(rt,&index.committed,&[ic1.0,ic2.0],&[ic1.1,ic2.1],tr);
    let auxiliary_opening=public::open_batch(rt,&aux,&[ac1.0,ac2.0],&[ac1.1,ac2.1],tr);
    let final_opening=public::open_batch(rt,&index.final_committed,&[fc],&[fv],tr);
    sparse_matrix::Proof{auxiliary:aux.key,rounds,endpoints:end,products,memory_endpoints,final_endpoints,opening,auxiliary_opening,final_opening}
}
#[cfg(test)]mod tests {
    use super::*;use crate::merkle::Hasher;
    #[test]fn endpoint_channels_share_one_reduction() {
        let mut rt=Runtime::new(8);
        let entries=(0..31).map(|i|(i%3,i,i%16)).collect();
        let index=Index::from_data(&mut rt,sparse_matrix::index_data(5,4,entries,16));
        let aux=(0..4).map(|_|rt.generate(index.channels[0].len,label)).collect::<Vec<_>>();rt.flush();
        let point=vec![label(3);index.key.entry_bits];let before=rt.command_count();
        assert_eq!(endpoints(&mut rt,&index,&aux,&point).len(),12);
        assert_eq!(rt.command_count()-before,8,"same-point endpoints were collected separately");
    }
    #[test]fn sharded_sparse_authentication_and_skew() {
        let row=vec![label(3);7];let col=vec![label(5);6];let rho=[label(7),label(11),label(13)];
        for n in [8,16] {
            let entries:Vec<_>=(0..127).map(|i|(i%3,i,if i<100{0}else{i%64})).collect();
            let source=sparse_matrix::index(7,6,entries.clone(),16);
            let expected=source.column_weights(&row,rho);let value=source.evaluate(&row,&col,rho);
            let mut rt=Runtime::new(n);let index=Index::from_data(&mut rt,sparse_matrix::index_data(7,6,entries,16));
            assert_eq!(index.key.pcs.root,source.key.pcs.root);assert_eq!(index.key.final_pcs.root,source.key.final_pcs.root);rt.seal();
            let weights=index.column_weights(&mut rt,&row,rho);assert_eq!(rt.get(weights,&(0..64).collect::<Vec<_>>()),expected);
            let h=Hasher::<H>::default();let proof=prove(&mut rt,&index,&row,&col,rho,value,&mut Transcript::new_global(&h,b"peer sparse"));
            sparse_matrix::verify(&index.key,&row,&col,rho,value,&proof,&mut Transcript::new_global(&h,b"peer sparse")).unwrap();
            let expected=sparse_matrix::prove(&source,&row,&col,rho,value,&mut Transcript::new_global(&h,b"peer sparse"));
            assert_eq!(proof.encode(),expected.encode());

        }
    }
}
