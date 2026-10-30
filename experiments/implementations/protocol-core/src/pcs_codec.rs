//! Complete standalone PCS serialization. Every path is explicit (no estimated multiproof size).
use crate::{protocol::Proof, setup::{Instance,Setup}, sha_zk::{Reader,encode_pcs}};

pub const PROOF_MAGIC: &[u8; 8] = b"B2PCS004";

pub fn encode_proof(proof:&Proof)->Vec<u8> {
    let inner=encode_pcs(proof);let mut b=PROOF_MAGIC.to_vec();
    b.extend((inner.len() as u64).to_le_bytes());b.extend(inner);b
}
pub fn decode_proof(setup:&Setup,b:&[u8])->Result<Proof,String> {
    let mut r=Reader(b);if r.take(PROOF_MAGIC.len())?!=PROOF_MAGIC {return Err("PCS proof magic".into());}
    let p=r.pcs(setup,true)?;if !r.0.is_empty(){return Err("PCS proof trailing bytes".into());}Ok(p)
}
pub fn decode_instance(setup:&Setup,b:&[u8])->Result<Instance,String> {
    let mut r=Reader(b);let r_h=r.fields(crate::field::LOG_D)?;
    let r_a=r.fields(setup.log_k())?;let r_b=r.fields(setup.params.ell)?;let s_x=r.field()?;
    if !r.0.is_empty(){return Err("PCS instance trailing bytes".into());}
    Ok(Instance{r_h,r_a,r_b,s_x})
}
