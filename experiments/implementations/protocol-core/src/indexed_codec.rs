//! Canonical indexed wrapper. The legacy inner format is never an independent
//! accepted statement here; B2IDX005 binds both matrix proofs and the approved key.
use crate::{indexed::{VerifierKey,MatrixProof},sha_zk::{Proof,Reader},params::{Params,ceil_log2},setup::Setup,public_pcs,sparse_matrix};
fn put(b:&mut Vec<u8>,x:usize){b.extend((x as u64).to_le_bytes());}
fn size(r:&mut Reader<'_>)->Result<usize,String>{usize::try_from(u64::from_le_bytes(r.take(8)?.try_into().unwrap())).map_err(|_|"length overflow".into())}
fn exact(r:&mut Reader<'_>,n:usize)->Result<(),String>{if size(r)?!=n{Err("noncanonical shape".into())}else{Ok(())}}
fn params(b:&mut Vec<u8>,p:&Params){for n in [p.n_parties,p.ell,p.beta,p.gamma,p.tau,p.salt_bytes]{put(b,n);}}
fn read_params(r:&mut Reader<'_>)->Result<Params,String>{let p=Params{n_parties:size(r)?,ell:size(r)?,beta:size(r)?,gamma:size(r)?,tau:size(r)?,salt_bytes:size(r)?};if !p.n_parties.is_power_of_two()||p.n_parties<8||p.n_parties>256||p.ell>=40||p.beta!=2||p.gamma<8||p.gamma>1<<20||p.tau<3||p.tau>=ceil_log2(p.gamma+2)||p.ell<=ceil_log2(p.gamma+2)||p.salt_bytes!=32{return Err("unsupported indexed parameters".into());}Ok(p)}
fn key(b:&mut Vec<u8>,k:&sparse_matrix::Key){b.extend(k.binding());}
fn read_public_key(r:&mut Reader<'_>)->Result<public_pcs::Key,String>{let log=size(r)?;let queries=size(r)?;let root=r.hash()?;if log<4||log>=60||queries==0||queries>1<<20{return Err("public key shape".into());}Ok(public_pcs::Key{log,queries,root})}
fn read_key(r:&mut Reader<'_>)->Result<sparse_matrix::Key,String>{let pcs=read_public_key(r)?;let row_bits=size(r)?;let col_bits=size(r)?;let entry_bits=size(r)?;let channel_bits=size(r)?;let final_pcs=read_public_key(r)?;
 let k=sparse_matrix::Key{row_bits,col_bits,entry_bits,channel_bits,pcs,final_pcs};if row_bits>=40||col_bits>=48||!k.valid(){return Err("matrix key shape".into());}Ok(k)}
pub fn encode_key(v:&VerifierKey)->Vec<u8>{let mut b=if v.keccak {b"KEYKIDX1".to_vec()}else{b"KEYIDX04".to_vec()};key(&mut b,&v.private);key(&mut b,&v.public);params(&mut b,&v.pcs.params);params(&mut b,&v.g.params);for n in [v.n,v.groups,v.base_row_bits,v.prefix.len()]{put(&mut b,n);}b.extend(&v.prefix);put(&mut b,v.gmap.len());for &x in &v.gmap{put(&mut b,x);}b}
pub fn decode_key(b:&[u8])->Result<VerifierKey,String>{let mut r=Reader(b);let keccak=match r.take(8)? {b"KEYIDX04"=>false,b"KEYKIDX1"=>true,_=>return Err("key magic".into())};let private=read_key(&mut r)?;let public=read_key(&mut r)?;let p=read_params(&mut r)?;let g=read_params(&mut r)?;let n=size(&mut r)?;let groups=size(&mut r)?;let base_row_bits=size(&mut r)?;let len=size(&mut r)?;let prefix=r.take(len)?.to_vec();if n!=p.n_parties||n!=g.n_parties||!groups.is_power_of_two()||groups>1<<20||base_row_bits>=40{return Err("key configuration".into());}
 let rb=base_row_bits+groups.trailing_zeros() as usize;let sc1=rb+(n/4).trailing_zeros() as usize;let sc2=8+p.ell;if private.row_bits!=rb||public.row_bits!=rb||private.col_bits!=sc2||public.col_bits!=9+groups.trailing_zeros() as usize{return Err("key dimensions".into());}
 exact(&mut r,4*sc1+3*sc2)?;let gmap=(0..4*sc1+3*sc2).map(|_|size(&mut r)).collect::<Result<Vec<_>,_>>()?;if gmap.iter().any(|&cell|cell>=g.k()*g.n())||!r.0.is_empty(){return Err("G map/key trailing bytes".into());}
 let layout=crate::params::Layout::verifier(&g);
 let mut seen=std::collections::HashSet::new();
 for &cell in &gmap {let (y,x)=(cell/g.n(),cell%g.n());if !seen.insert(cell)||layout.pad.binary_search(&x).is_ok()||layout.masks.iter().flatten().any(|m|m.y==y&&m.x==x){return Err("G map must contain distinct Data cells".into());}}
 Ok(VerifierKey{private,public,pcs:Setup::verifier(p),g:Setup::verifier(g),gmap,n,groups,base_row_bits,prefix,keccak})}
fn read_opening(r:&mut Reader<'_>,k:&public_pcs::Key)->Result<public_pcs::Proof,String>{let f=k.log-3;exact(r,f)?;exact(r,f)?;exact(r,8)?;exact(r,k.queries)?;let roots=(0..f).map(|_|r.hash()).collect::<Result<_,_>>()?;let rounds=(0..f).map(|_|Ok((r.field()?,r.field()?))).collect::<Result<_,String>>()?;let tail=r.fields(8)?;let mut openings=vec![];for _ in 0..k.queries{exact(r,f)?;let mut q=vec![];for j in 0..f{let pair=r.fields(2)?.try_into().unwrap();exact(r,k.log+1-j)?;let path=(0..k.log+1-j).map(|_|r.hash()).collect::<Result<_,_>>()?;q.push(public_pcs::Query{pair,path});}openings.push(q);}Ok(public_pcs::Proof{roots,rounds,tail,openings})}
fn read_product(r:&mut Reader<'_>,depth:usize)->Result<crate::product_tree::Proof,String>{let roots=r.fields(8)?.try_into().unwrap();exact(r,depth)?;let mut layers=vec![];for i in 0..depth{exact(r,3+i)?;let rounds=(0..3+i).map(|_|Ok(r.fields(4)?.try_into().unwrap())).collect::<Result<_,String>>()?;let endpoints=r.fields(2)?.try_into().unwrap();layers.push(crate::product_tree::Layer{rounds,endpoints});}Ok(crate::product_tree::Proof{roots,layers})}
fn read_sparse(r:&mut Reader<'_>,k:&sparse_matrix::Key)->Result<sparse_matrix::Proof,String>{let auxiliary=read_public_key(r)?;if auxiliary.log!=k.entry_bits+2||auxiliary.queries!=k.pcs.queries{return Err("auxiliary key shape".into());}exact(r,k.entry_bits)?;let rounds=(0..k.entry_bits).map(|_|r.fields(6)).collect::<Result<_,_>>()?;let endpoints=r.fields(19)?;let reads=read_product(r,k.entry_bits)?;let table=read_product(r,k.table_bits())?;let memory_endpoints=r.fields(19)?;let final_endpoints=r.fields(4)?.try_into().unwrap();let opening=read_opening(r,&k.pcs)?;let auxiliary_opening=read_opening(r,&auxiliary)?;let final_opening=read_opening(r,&k.final_pcs)?;Ok(sparse_matrix::Proof{auxiliary,rounds,endpoints,reads,table,memory_endpoints,final_endpoints,opening,auxiliary_opening,final_opening})}
pub fn encode_proof(core:&Proof,m:&MatrixProof)->Vec<u8>{let mut b=b"B2IDX005".to_vec();let inner=core.to_bytes();put(&mut b,inner.len());b.extend(inner);b.extend(m.encode());b}
pub fn decode_proof(v:&VerifierKey,b:&[u8])->Result<(Proof,MatrixProof),String>{let mut r=Reader(b);if r.take(8)?!=b"B2IDX005"{return Err("indexed proof magic".into());}let len=size(&mut r)?;let core=Proof::from_shape(v.sc1_len(),v.sc2_len(),v.n,&v.g,&v.pcs,r.take(len)?)?;let public_value=r.field()?;let weight=r.field()?;let len=size(&mut r)?;let mut c=Reader(r.take(len)?);exact(&mut c,v.public.col_bits)?;let rounds=(0..v.public.col_bits).map(|_|Ok(c.fields(3)?.try_into().unwrap())).collect::<Result<_,String>>()?;let w=c.field()?;let matrix=read_sparse(&mut c,&v.public)?;if !c.0.is_empty(){return Err("public contraction trailing bytes".into());}let input=sparse_matrix::Contraction{rounds,weight:w,matrix};let private=read_sparse(&mut r,&v.private)?;if !r.0.is_empty(){return Err("indexed trailing bytes".into());}Ok((core,MatrixProof{public_value,input,weight,private}))}

#[cfg(test)]
mod global_capacity_tests {
 use super::*;
 #[test]
 fn previous_indexed_transcript_format_is_rejected_before_decoding() {
  let cfg=crate::sha_zk::Config::synthetic(8,2,16,3,48);
  let key=crate::indexed::Index::new(&cfg,16).verifier_key(&cfg);
  assert!(matches!(decode_proof(&key,b"B2IDX004"),Err(e) if e=="indexed proof magic"));
 }
 #[test]
 fn g_map_decoder_requires_unique_data_cells_in_all_rows() {
  let cfg=crate::sha_zk::Config::synthetic(8,2,16,3,48);
  let index=crate::indexed::Index::new(&cfg,16);
  let mut key=index.verifier_key(&cfg);
  assert!(key.gmap.iter().any(|&cell|cell>=key.g.params.n()));
  let bytes=encode_key(&key);assert!(decode_key(&bytes).is_ok());
  let mut old=bytes.clone();old[..8].copy_from_slice(b"KEYIDX03");assert!(decode_key(&old).is_err());
  let saved=key.gmap[0];
  for cell in [key.gmap[1],key.g.params.k()*key.g.params.n(),key.g.layout.pad[0],key.g.layout.masks.iter().flatten().next().map(|m|m.y*key.g.params.n()+m.x).unwrap()] {
   key.gmap[0]=cell;assert!(decode_key(&encode_key(&key)).is_err());
  }
  key.gmap[0]=saved;assert!(decode_key(&encode_key(&key)).is_ok());
 }
}
