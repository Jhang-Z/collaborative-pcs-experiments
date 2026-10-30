//! Indexed ZK composition. Online verification takes no circuit or full index.
use crate::{field::{Field,L,eq_expand},fs::Transcript,merkle::{Hash,Hasher},setup::{Setup,Instance},
 sha_zk::{self,Config},sparse_matrix::{self,Index as SparseIndex},spartan::{eq_eval,interp},protocol,zk};
use binius_hash::Blake3HashSuite as H;
use rand::{SeedableRng,rngs::StdRng};use std::io::Read;
const ZERO:Hash=[0;32];
fn bytes(v:&[L])->&[u8]{bytemuck::cast_slice(v)}
pub struct Index {pub private:SparseIndex,pub public:SparseIndex}
pub struct VerifierKey {
 pub private:sparse_matrix::Key,pub public:sparse_matrix::Key,
 pub pcs:Setup,pub g:Setup,pub gmap:Vec<usize>,
 pub n:usize,pub groups:usize,pub base_row_bits:usize,pub prefix:Vec<u8>,
 pub keccak:bool,
}
#[derive(Clone)]
pub struct MatrixProof {pub public_value:L,pub input:sparse_matrix::Contraction,pub weight:L,pub private:sparse_matrix::Proof}
impl MatrixProof {pub fn encode(&self)->Vec<u8>{let mut b=bytes(&[self.public_value,self.weight]).to_vec();let input=self.input.encode();b.extend((input.len() as u64).to_le_bytes());b.extend(input);b.extend(self.private.encode());b}}
fn statement(prefix:&[u8],a:&sparse_matrix::Key,b:&sparse_matrix::Key,d:&[[u8;32]],keccak:bool)->Vec<u8>{let mut v=if keccak {b"indexed-keccak-f1600-256-v1-memory-blake3".to_vec()}else{b"indexed-zk-v2-memory-blake3".to_vec()};v.extend((prefix.len() as u64).to_le_bytes());v.extend(prefix);v.extend(a.binding());v.extend(b.binding());v.extend((d.len() as u64).to_le_bytes());v.extend(d.iter().flatten());v}
impl Index {
 pub fn new(cfg:&Config,queries:usize)->Self {
  let base=&cfg.circuit.base;let(mut private,mut public)=(vec![],vec![]);
  for gg in 0..cfg.groups{for(t,mat)in [&base.a,&base.b,&base.c].into_iter().enumerate(){for(j,row)in mat.iter().enumerate(){for &p in row {
   let r=j+gg*base.m0();if p<cfg.circuit.private_len{private.push((t,r,cfg.map[p+gg*base.n0()]));}
   else{assert!(p-cfg.circuit.private_len<257);public.push((t,r,p-cfg.circuit.private_len+gg*512));}
  }}}}
  let rb=base.log_m0+cfg.groups.trailing_zeros() as usize;
  Self{private:sparse_matrix::index(rb,cfg.sc2_len(),private,queries),public:sparse_matrix::index(rb,9+cfg.groups.trailing_zeros() as usize,public,queries)}
 }
 pub fn statement(&self,cfg:&Config,d:&[[u8;32]])->Vec<u8>{statement(&cfg.statement(&[]),&self.private.key,&self.public.key,d,cfg.circuit.keccak)}
 pub fn verifier_key(&self,cfg:&Config)->VerifierKey{VerifierKey{private:self.private.key.clone(),public:self.public.key.clone(),pcs:Setup::verifier(cfg.pcs.params.clone()),g:Setup::verifier(cfg.g.params.clone()),gmap:cfg.gmap.clone(),n:cfg.ctx.n,groups:cfg.groups,base_row_bits:cfg.circuit.base.log_m0,prefix:cfg.statement(&[]),keccak:cfg.circuit.keccak}}
}
impl VerifierKey {
 pub fn batch(&self)->usize{self.groups*self.n/4}
 pub fn sc1_len(&self)->usize{self.base_row_bits+self.groups.trailing_zeros() as usize+(self.n/4).trailing_zeros() as usize}
 pub fn sc2_len(&self)->usize{8+self.pcs.params.ell}
 fn statement(&self,d:&[[u8;32]])->Vec<u8>{statement(&self.prefix,&self.private,&self.public,d,self.keccak)}
}
/// At most 512*groups values; linear only in the public inputs (257 bits/copy).
/// The authenticated key fixes whether bytes encode SHA words or Keccak bits.
pub fn public_vector(groups:usize,k:usize,ry:&[L],d:&[[u8;32]],keccak:bool)->Vec<L>{
 assert_eq!(d.len(),groups*k);let ey=eq_expand(ry);let mut v=vec![L::ZERO;512*groups];
 for y in 0..k{for gg in 0..groups{v[gg*512]+=ey[y];for t in 0..8{let chunk=d[gg+groups*y][4*t..4*t+4].try_into().unwrap();let word=if keccak {u32::from_le_bytes(chunk)}else{u32::from_be_bytes(chunk)};for j in 0..32{if word>>j&1==1{v[gg*512+1+t*32+j]+=ey[y];}}}}}v
}
pub fn prove(cfg:&Config,index:&Index,seed:u64)->(sha_zk::Run,MatrixProof){let mut entropy=[0;32];std::fs::File::open("/dev/urandom").unwrap().read_exact(&mut entropy).unwrap();let(run,m)=sha_zk::prove_core(cfg,seed,StdRng::from_seed(entropy),Some(index));(run,m.unwrap())}
/// Prove the ordered external SHA-256 messages with fresh OS-seeded proof randomness.
/// This entry point omits the legacy internal verification; callers must run `verify`.
/// Witness/sharing/preprocessing remain included until the preparation split is implemented.
pub fn prove_messages(cfg:&Config,index:&Index,messages:&[[u8;32]])->Result<(sha_zk::Run,MatrixProof),String>{
 if messages.len()!=cfg.batch(){return Err("SHA message count does not match configuration".into());}
 let mut entropy=[0;32];std::fs::File::open("/dev/urandom").and_then(|mut f|f.read_exact(&mut entropy)).map_err(|e|format!("OS randomness: {e}"))?;
 let(run,m)=sha_zk::prove_core_messages(cfg,messages,StdRng::from_seed(entropy),index);Ok((run,m.expect("indexed matrix proof")))
}
pub fn verify(cfg: &VerifierKey, digests: &[[u8; 32]], proof: &sha_zk::Proof, matrix:&MatrixProof) -> Result<(), String> {
    if digests.len() != cfg.batch()
        || proof.sc1.len() != cfg.sc1_len()
        || proof.sc2.len() != cfg.sc2_len()
        || proof.pcs.roots.len() != cfg.pcs.params.folds()
        || proof.g.roots.len() != cfg.g.params.folds()
        || proof.conversions.len() != 2
        || proof.conversions.iter().any(|v| v.len() != cfg.n)
    {
        return Err("shape".into());
    }
    let h = Hasher::<H>::default();
    let mut tr = Transcript::new_global(&h, &cfg.statement(digests));
    let top = h.hash(&[b"v04-top", &proof.pcs.roots[0], &proof.g.roots[0]]);
    if top != proof.top {
        return Err("top root".into());
    }
    tr.absorb(
        b"initial roots",
        &[proof.pcs.roots[0], proof.g.roots[0]].concat(),
    );
    let mut c = tr.round(&top, &proof.nonce);
    let tau: Vec<_> = (0..cfg.sc1_len()).map(|_| c.field()).collect();
    let lambda1 = tr.round(&ZERO, bytes(&[proof.h1])).field();
    if lambda1 == L::ZERO {
        return Err("lambda1 excluded".into());
    }
    let mut claim = lambda1 * proof.h1;
    let mut rx = Vec::new();
    for (round, s) in proof.sc1.iter().enumerate() {
        if round == cfg.base_row_bits + cfg.groups.trailing_zeros() as usize {
            tr.absorb(b"conversions", bytes(&proof.conversions.concat()));
        }
        if s[0] + s[1] != claim {
            return Err("SC1 sum".into());
        }
        let r = tr.round(&ZERO, bytes(s)).field();
        if r == L::ONE { return Err("SC1 excluded challenge".into()); }
        claim = interp(s, r);
        rx.push(r);
    }
    let v = proof.endpoints;
    if claim != eq_eval(&tau, &rx) * (v[0] * v[1] + v[2]) + lambda1 * proof.y1 {
        return Err("SC1 endpoint".into());
    }
    let nvcol = cfg.base_row_bits + cfg.groups.trailing_zeros() as usize;
    let (rcol, ry) = rx.split_at(nvcol);
    let mut ep = v.to_vec();
    ep.push(proof.y1);
    let mut c = tr.round(&ZERO, bytes(&ep));
    let rho: [L; 3] = std::array::from_fn(|_| c.field());
    let public=matrix.public_value;
    let input=public_vector(cfg.groups,cfg.n/4,ry,digests,cfg.keccak);
    sparse_matrix::contract_verify(&cfg.public,rcol,rho,&input,public,&matrix.input,&mut tr)?;
    let mut claim = rho.iter().zip(v).map(|(&a, b)| a * b).sum::<L>() + public;
    let lambda2 = tr.round(&ZERO, bytes(&[proof.h2])).field();
    if lambda2 == L::ZERO {
        return Err("lambda2 excluded".into());
    }
    claim += lambda2 * proof.h2;
    let mut rp = Vec::new();
    for s in &proof.sc2 {
        if s[0] + s[1] != claim {
            return Err("SC2 sum".into());
        }
        let r = tr.round(&ZERO, bytes(s)).field();
        if r == L::ONE { return Err("SC2 excluded challenge".into()); }
        claim = interp(s, r);
        rp.push(r);
    }
    let wr=matrix.weight;
    if claim != wr * proof.value + lambda2 * proof.y2 {
        return Err("SC2 endpoint".into());
    }
    tr.absorb(b"private matrix endpoint",bytes(&[wr, proof.value, proof.y2]));
    sparse_matrix::verify(&cfg.private,rcol,&rp,rho,wr,&matrix.private,&mut tr)?;
    let eta = tr.round(&ZERO, bytes(&[proof.value, proof.y2])).field();
    let mut gw = zk::selector_weights(&rx, 3);
    gw.extend(zk::selector_weights(&rp, 2).into_iter().map(|x| eta * x));
    zk::verify_g(
        &cfg.g,
        &cfg.gmap,
        &gw,
        proof.y1 + eta * proof.y2,
        &proof.g,
        &mut tr,
    )?;
    tr.absorb(b"G opening", &sha_zk::encode_pcs(&proof.g));
    let inst = Instance {
        r_h: rp[..8].to_vec(),
        r_a: ry.to_vec(),
        r_b: rp[8..].to_vec(),
        s_x: proof.value,
    };
    tr.absorb(b"main instance", &inst.to_bytes());
    protocol::verify_in::<H>(&cfg.pcs, &inst, &proof.pcs, &mut tr, zk::BIT_ROLE)?;
    Ok(())
}

#[cfg(test)]mod tests {
 use super::*;
 #[test]fn keccak_public_vector_uses_byte_little_endian_bits(){
  let mut digests=vec![[0u8;32];2];digests[0][0]=1;
  let values=public_vector(1,2,&[L::ZERO],&digests,true);
  assert_eq!(values[0],L::ONE,"constant public wire");
  assert_eq!(values[1],L::ONE,"Keccak byte 0 bit 0 is public wire 1");
  assert_eq!(values[25],L::ZERO,"SHA word-byte reversal must not move Keccak bit 0 to bit 24");
 }
 #[test]fn public_output_orders_and_nonboolean_slot_mixing(){
  let r=crate::field::from_words([7,0]);
  let mut digests=vec![[0u8;32];4];
  digests[0][0]=1;digests[1][31]=128;digests[2][3]=128;
  digests[3][0]=1;digests[3][31]=128;
  for (keccak,positions) in [(true,[0,31,255]),(false,[24,7,231])] {
   let actual=public_vector(2,2,&[r],&digests,keccak);
   let mut expected=vec![L::ZERO;1024];
   expected[0]=L::ONE;expected[512]=L::ONE;
   expected[1+positions[0]]=L::ONE+r;
   expected[1+positions[1]]=r;
   expected[513+positions[2]]=L::ONE;
   expected[513+positions[0]]=r;
   assert_eq!(actual,expected);
  }
 }
 #[test]fn indexed_key_binds_public_output_encoding(){
  let cfg=Config::synthetic(8,1,16,3,32);let index=Index::new(&cfg,16);
  let mut key=index.verifier_key(&cfg);let digests=vec![[0u8;32];2];
  let sha_statement=key.statement(&digests);
  let sha=crate::indexed_codec::encode_key(&key);
  assert_eq!(&sha[..8],b"KEYIDX04");
  assert!(!crate::indexed_codec::decode_key(&sha).unwrap().keccak);
  key.keccak=true;
  let keccak=crate::indexed_codec::encode_key(&key);
  assert_eq!(&keccak[..8],b"KEYKIDX1");
  let decoded=crate::indexed_codec::decode_key(&keccak).unwrap();
  assert!(decoded.keccak);
  assert_eq!(crate::indexed_codec::encode_key(&decoded),keccak);
  assert_ne!(sha_statement,decoded.statement(&digests));
 }
 #[test]fn full_indexed_zk_compact_verification_and_mutations(){
  let cfg=Config::synthetic(8,1,16,3,32);let index=Index::new(&cfg,32);let vk=index.verifier_key(&cfg);
  let(run,m)=prove(&cfg,&index,91);drop(index);drop(cfg);
  let key_bytes=crate::indexed_codec::encode_key(&vk);
  let vk=crate::indexed_codec::decode_key(&key_bytes).unwrap();
  let proof_bytes=crate::indexed_codec::encode_proof(&run.proof,&m);
  let(core,mat)=crate::indexed_codec::decode_proof(&vk,&proof_bytes).unwrap();
  assert!(verify(&vk,&run.digests,&core,&mat).is_ok());
  assert_eq!(crate::indexed_codec::encode_proof(&core,&mat),proof_bytes);
  assert!(crate::indexed_codec::decode_proof(&vk,&proof_bytes[..proof_bytes.len()-1]).is_err());
  assert!(vk.pcs.layout.owned.is_empty()&&vk.pcs.layout.is_pad.is_empty());
  assert!(verify(&vk,&run.digests,&run.proof,&m).is_ok());
  let mut bad=m.clone();bad.weight+=L::ONE;assert!(verify(&vk,&run.digests,&run.proof,&bad).is_err());
  let mut bad=m.clone();bad.public_value+=L::ONE;assert!(verify(&vk,&run.digests,&run.proof,&bad).is_err());
  let mut bad=m.clone();bad.private.opening.openings[0][0].pair[0]+=L::ONE;assert!(verify(&vk,&run.digests,&run.proof,&bad).is_err());
  let mut bad=run.proof.clone();bad.nonce[0]^=1;assert!(verify(&vk,&run.digests,&bad,&m).is_err());
  let mut bad=run.digests.clone();bad[0][0]^=1;assert!(verify(&vk,&bad,&run.proof,&m).is_err());
  let mut wrong=vk;wrong.keccak=true;assert!(verify(&wrong,&run.digests,&run.proof,&m).is_err());
  wrong.keccak=false;wrong.private.pcs.root[0]^=1;assert!(verify(&wrong,&run.digests,&run.proof,&m).is_err());
 }
}
