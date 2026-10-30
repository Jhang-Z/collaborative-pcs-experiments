//! Fixed Keccak-f[1600]/256 relation with structured public matrix evaluation.
//!
//! The verifier rebuilds the canonical Keccak circuit and physical layout. This is
//! a Keccak-specific verifier, not the compact generic indexed verifier. Key
//! construction includes the public circuit/layout preparation cost.
use crate::{
    merkle::{Hash, Hasher},
    sha_zk::{self, Config, MatrixEvaluation, Proof, Reader},
};
use binius_hash::Blake3HashSuite as H;




const KEY_MAGIC: &[u8; 8] = b"KEYKEC01";
const PROOF_MAGIC: &[u8; 8] = b"B2KEC001";
pub const MAX_INSTANCES: usize = 4096;
// This revision fixes ShaCircuit::new_zk, the 256-bit packing/map allocator,
// beta=2, 32-byte salts, field/hash suites, and both coefficient-mask selectors.
// A change to that relation or layout requires a new revision and format.
const RELATION: &[u8] = b"keccak-f1600-truncated256-200b-private-32b-public-canonical-zk-layout-v4-global-capacity-cubes-multirow-g-f2^256-blake3-beta2-salt32";
const DOMAIN: &[u8] = b"structured-keccak256-zk-v4-global-capacity-cubes-multirow-g-blake3";

/// Constructible only from bounded parameters of the fixed public relation.
/// No caller-provided circuit, index, or physical-address map is accepted.
pub struct VerifierKey {
    cfg: Config,
    binding: Hash,
}

fn relation_id() -> Hash {
    Hasher::<H>::default().hash(&[b"structured-keccak-relation", RELATION])
}

fn validate_parameters(n: usize, groups: usize, gamma: usize, tau: usize) -> Result<(), String> {
    // Check bounds before constructing a circuit, shifting, or allocating a map.
    if !matches!(n, 8 | 16 | 32 | 64 | 128 | 256) || !groups.is_power_of_two() {
        return Err("unsupported structured Keccak party/group count".into());
    }
    if groups > MAX_INSTANCES / (n / 4) {
        return Err("unsupported structured Keccak party/group count".into());
    }
    let batch = groups * (n / 4); // bounded before multiplication and allocation
    let formal = gamma == 871 && tau == 4 && (8..=MAX_INSTANCES).contains(&batch);
    let development = n == 8 && groups == 1 && gamma == 16 && tau == 3;
    if !formal && !development {
        return Err("unsupported structured Keccak parameters: use the formal configuration or N8/B2/gamma16/tau3 development configuration".into());
    }
    Ok(())
}

impl VerifierKey {
    pub fn new(n: usize, groups: usize, gamma: usize, tau: usize) -> Result<Self, String> {
        validate_parameters(n, groups, gamma, tau)?;
        let cfg = Config::new_keccak(n, groups, gamma, tau);
        let mut key = Self {
            cfg,
            binding: [0; 32],
        };
        key.binding = Hasher::<H>::default().hash(&[b"structured-keccak-key", &encode_key(&key)]);
        Ok(key)
    }

    pub fn config(&self) -> &Config {
        &self.cfg
    }

    pub fn statement(&self, digests: &[[u8; 32]]) -> Vec<u8> {
        let mut statement = DOMAIN.to_vec();
        statement.extend_from_slice(&self.binding);
        statement.extend_from_slice(&(digests.len() as u64).to_le_bytes());
        statement.extend(digests.iter().flatten());
        statement
    }
}

/// Canonical key: magic, fixed relation identifier, and four bounded parameters.
/// The circuit, map, PCS layout, and mask-coefficient layout are derived locally.
pub fn encode_key(key: &VerifierKey) -> Vec<u8> {
    let cfg = key.config();
    let mut bytes = KEY_MAGIC.to_vec();
    bytes.extend_from_slice(&relation_id());
    for value in [
        cfg.ctx.n,
        cfg.groups,
        cfg.pcs.params.gamma,
        cfg.pcs.params.tau,
    ] {
        bytes.extend_from_slice(&(value as u64).to_le_bytes());
    }
    bytes
}

pub fn decode_key(bytes: &[u8]) -> Result<VerifierKey, String> {
    let mut reader = Reader(bytes);
    if reader.take(8)? != KEY_MAGIC {
        return Err("structured Keccak key magic".into());
    }
    if reader.hash()? != relation_id() {
        return Err("structured Keccak relation/version".into());
    }
    let mut values = [0; 4];
    for value in &mut values {
        *value = usize::try_from(u64::from_le_bytes(reader.take(8)?.try_into().unwrap()))
            .map_err(|_| "structured Keccak parameter overflow")?;
    }
    if !reader.0.is_empty() {
        return Err("structured Keccak key trailing bytes".into());
    }
    VerifierKey::new(values[0], values[1], values[2], values[3])
}

pub fn encode_proof(key: &VerifierKey, proof: &Proof) -> Vec<u8> {
    let inner = proof.to_bytes();
    let mut bytes = PROOF_MAGIC.to_vec();
    bytes.extend_from_slice(&key.binding);
    bytes.extend_from_slice(&(inner.len() as u64).to_le_bytes());
    bytes.extend(inner);
    bytes
}

pub fn decode_proof(key: &VerifierKey, bytes: &[u8]) -> Result<Proof, String> {
    let mut reader = Reader(bytes);
    if reader.take(8)? != PROOF_MAGIC {
        return Err("structured Keccak proof magic".into());
    }
    if reader.hash()? != key.binding {
        return Err("structured Keccak proof/key binding".into());
    }
    let len = usize::try_from(u64::from_le_bytes(reader.take(8)?.try_into().unwrap()))
        .map_err(|_| "structured Keccak proof length overflow")?;
    let inner = reader.take(len)?;
    if !reader.0.is_empty() {
        return Err("structured Keccak proof trailing bytes".into());
    }
    Proof::from_bytes(key.config(), inner)
}

/// Checks both masked sumchecks, both PCS openings, and both public matrix values.
/// Reads only the fixed public key, ordered public digests, and complete proof.
pub fn verify(key: &VerifierKey, digests: &[[u8; 32]], proof: &Proof) -> Result<(), String> {
    sha_zk::verify_with_statement(
        key.config(),
        digests,
        proof,
        &key.statement(digests),
        MatrixEvaluation::Structured,
    )
}


#[cfg(test)] mod tests {
 use super::*;
 #[test] fn formal_batch_boundary_tracks_party_packing() {
  for n in [8,16,32,64,128,256] {
   assert!(validate_parameters(n,4096/(n/4),871,4).is_ok(),"4096 at N={n}");
   assert!(validate_parameters(n,8192/(n/4),871,4).is_err());
   assert!(validate_parameters(n,2048/(n/4),871,4).is_ok());
  }
  for n in [0,4,31,512,usize::MAX] { assert!(validate_parameters(n,1,871,4).is_err()); }
  for groups in [0,3,usize::MAX,1usize<<(usize::BITS-1)] {
   assert!(validate_parameters(32,groups,871,4).is_err());
  }
  assert!(validate_parameters(32,512,16,3).is_err());
  assert!(validate_parameters(8,1,16,3).is_ok());
 }
 #[test] fn canonical_keccak_key_rejects_sha_and_binds_output_relation() {
  let k=VerifierKey::new(8,1,16,3).unwrap();let bytes=encode_key(&k);
  assert_eq!(&bytes[..8],b"KEYKEC01");assert!(k.config().circuit.keccak);
  assert_eq!(encode_key(&decode_key(&bytes).unwrap()),bytes);
  let mut bad=bytes.clone();bad[..8].copy_from_slice(b"KEYSHA03");assert!(decode_key(&bad).is_err());
  let mut bad=bytes;bad[9]^=1;assert!(decode_key(&bad).is_err());
 }
}
