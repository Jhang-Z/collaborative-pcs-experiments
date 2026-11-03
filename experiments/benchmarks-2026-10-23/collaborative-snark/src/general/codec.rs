//! Separate general-circuit envelope; the old inner encoding is never accepted alone.
use crate::{indexed_codec,sha_zk::{self,Reader},setup::Setup};
use super::{proof::{VerifierKey,Proof,MatrixProof},public_input,onehot};
fn put(b:&mut Vec<u8>,x:usize){b.extend((x as u64).to_le_bytes());}
fn size(r:&mut Reader<'_>)->Result<usize,String>{usize::try_from(u64::from_le_bytes(r.take(8)?.try_into().unwrap())).map_err(|_|"length overflow".into())}
pub fn encode_key(v:&VerifierKey)->Vec<u8> {
    let mut b=b"GENKEY05".to_vec();b.extend(v.circuit_hash);
    for x in [v.n,v.row_bits,v.physical_bits] {put(&mut b,x);}
    indexed_codec::params(&mut b,&v.pcs.params);indexed_codec::params(&mut b,&v.g.params);
    b.extend(v.private.binding());b.extend(v.public.binding());
    put(&mut b,v.gmap.len());for &x in &v.gmap {put(&mut b,x);}b
}
pub fn decode_key(b:&[u8])->Result<VerifierKey,String> {
    let mut r=Reader(b);if r.take(8)?!=b"GENKEY05" {return Err("general key magic".into());}
    let circuit_hash=r.hash()?;let n=size(&mut r)?;let row_bits=size(&mut r)?;let physical_bits=size(&mut r)?;
    let p=indexed_codec::read_params(&mut r)?;let g=indexed_codec::read_params(&mut r)?;
    let private=read_key(&mut r)?;let public=indexed_codec::read_public_key(&mut r)?;
    if n!=private.params.n_parties||private.params.gamma!=p.gamma||private.params.tau!=p.tau||n!=p.n_parties||n!=g.n_parties||row_bits>40||row_bits<(n/4).ilog2() as usize||physical_bits!=8+p.ell||
        private.row_bits!=row_bits||public.log!=row_bits+3||public.queries!=p.gamma||private.col_bits!=physical_bits+(n/4).ilog2() as usize {
        return Err("general key dimensions".into());
    }
    let len=4*row_bits+3*private.col_bits;
    if size(&mut r)?!=len {return Err("general G map shape".into());}
    let gmap=(0..len).map(|_|size(&mut r)).collect::<Result<Vec<_>,_>>()?;
    if !r.0.is_empty() {return Err("general key trailing bytes".into());}
    let layout=crate::params::Layout::verifier(&g);let mut seen=std::collections::HashSet::new();
    for &cell in &gmap {
        let (y,x)=(cell/g.n(),cell%g.n());
        if y>=g.k()||!seen.insert(cell)||layout.pad.binary_search(&x).is_ok()||
            layout.masks.iter().flatten().any(|m|m.y==y&&m.x==x) {return Err("general G map Data cells".into());}
    }
    Ok(VerifierKey{n,row_bits,physical_bits,pcs:Setup::verifier_compact(p),g:Setup::verifier_compact(g),gmap,private,public,circuit_hash})
}
pub fn encode_proof(p:&Proof)->Vec<u8> {
    let mut b=b"GENPRF05".to_vec();let core=p.core.to_bytes();put(&mut b,core.len());b.extend(core);
    b.extend(bytemuck::cast_slice(&p.column_conversion));b.extend(p.matrix.encode());b
}
pub fn decode_proof(v:&VerifierKey,b:&[u8])->Result<Proof,String> {
    let mut r=Reader(b);if r.take(8)?!=b"GENPRF05" {return Err("general proof magic".into());}
    let len=size(&mut r)?;
    let core=sha_zk::Proof::from_shape(v.row_bits,v.physical_bits+v.slot_bits(),v.n,&v.g,&v.pcs,r.take(len)?)?;
    let column_conversion=r.fields(v.n)?;
    let public_value=r.field()?;let weight=r.field()?;let len=size(&mut r)?;let mut c=Reader(r.take(len)?);
    let values=c.fields(6)?.try_into().unwrap();let opening=indexed_codec::read_opening(&mut c,&v.public)?;
    if !c.0.is_empty() {return Err("general public columns trailing bytes".into());}
    let input=public_input::Proof{values,opening};let private=read_sparse(&mut r,&v.private)?;
    if !r.0.is_empty() {return Err("general proof trailing bytes".into());}
    Ok(Proof{core,column_conversion,matrix:MatrixProof{public_value,input,weight,private}})
}

fn read_key(r:&mut Reader<'_>)->Result<onehot::Key,String>{
 let row_bits=size(r)?;let col_bits=size(r)?;let entry_bits=size(r)?;let block_bits=size(r)?;
 let counts=[size(r)?,size(r)?,size(r)?];let params=indexed_codec::read_params(r)?;let root=r.hash()?;
 let k=onehot::Key{row_bits,col_bits,entry_bits,block_bits,counts,params,root};
 if !k.valid(){return Err("onehot matrix key shape".into());}Ok(k)
}
fn read_sparse(r:&mut Reader<'_>,k:&onehot::Key)->Result<onehot::Proof,String>{
 let rounds=(0..k.entry_bits).map(|_|r.fields(k.blocks()+2)).collect::<Result<_,_>>()?;
 let endpoints=r.fields(k.blocks())?;
 let reduction=(0..k.block_bits+k.selector_bits()).map(|_|r.fields(3).map(|v|v.try_into().unwrap())).collect::<Result<_,_>>()?;
 let evaluation=r.field()?;let opening=r.pcs(&Setup::verifier_compact(k.params.clone()),true)?;
 Ok(onehot::Proof{rounds,endpoints,reduction,evaluation,opening})
}
