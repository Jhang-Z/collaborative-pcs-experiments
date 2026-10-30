//! Fixed SHA-256/32-byte relation with structured public matrix evaluation.
//!
//! The verifier rebuilds the canonical SHA circuit and physical layout. This is
//! a SHA-specific verifier, not the compact generic indexed verifier. Key
//! construction includes the public circuit/layout preparation cost.
use crate::{
    merkle::{Hash, Hasher},
    sha_zk::{self, Config, MatrixEvaluation, Proof, Reader, Run},
};
use binius_hash::Blake3HashSuite as H;
use rand::{SeedableRng, rngs::StdRng};
use sha2::{Digest, Sha256};
use std::io::Read;

const KEY_MAGIC: &[u8; 8] = b"KEYSHA03";
const PROOF_MAGIC: &[u8; 8] = b"B2SIMD04";
// This revision fixes ShaCircuit::new_zk, the 256-bit packing/map allocator,
// beta=2, 32-byte salts, field/hash suites, and both coefficient-mask selectors.
// A change to that relation or layout requires a new revision and format.
const RELATION: &[u8] = b"sha256-32b-canonical-zk-layout-v4-global-capacity-cubes-multirow-g-f2^256-blake3-beta2-salt32";
const DOMAIN: &[u8] = b"structured-sha256-zk-v4-global-capacity-cubes-multirow-g-blake3";

/// Constructible only from bounded parameters of the fixed public relation.
/// No caller-provided circuit, index, or physical-address map is accepted.
pub struct VerifierKey {
    cfg: Config,
    binding: Hash,
}

fn relation_id() -> Hash {
    Hasher::<H>::default().hash(&[b"structured-sha-relation", RELATION])
}

fn validate_parameters(n: usize, groups: usize, gamma: usize, tau: usize) -> Result<(), String> {
    // Check bounds before constructing a circuit, shifting, or allocating a map.
    if !matches!(n, 8 | 16 | 32 | 64 | 128 | 256) || !groups.is_power_of_two() || groups > 128 {
        return Err("unsupported structured SHA party/group count".into());
    }
    let batch = groups * (n / 4); // bounded above by 8192 by the preceding check
    let formal = gamma == 871 && tau == 4 && (8..=256).contains(&batch);
    let development = n == 8 && groups == 1 && gamma == 16 && tau == 3;
    if !formal && !development {
        return Err("unsupported structured SHA parameters: use the formal configuration or N8/B2/gamma16/tau3 development configuration".into());
    }
    Ok(())
}

impl VerifierKey {
    pub fn new(n: usize, groups: usize, gamma: usize, tau: usize) -> Result<Self, String> {
        validate_parameters(n, groups, gamma, tau)?;
        let cfg = Config::new(n, groups, gamma, tau);
        let mut key = Self {
            cfg,
            binding: [0; 32],
        };
        key.binding = Hasher::<H>::default().hash(&[b"structured-sha-key", &encode_key(&key)]);
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
        return Err("structured SHA key magic".into());
    }
    if reader.hash()? != relation_id() {
        return Err("structured SHA relation/version".into());
    }
    let mut values = [0; 4];
    for value in &mut values {
        *value = usize::try_from(u64::from_le_bytes(reader.take(8)?.try_into().unwrap()))
            .map_err(|_| "structured SHA parameter overflow")?;
    }
    if !reader.0.is_empty() {
        return Err("structured SHA key trailing bytes".into());
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
        return Err("structured SHA proof magic".into());
    }
    if reader.hash()? != key.binding {
        return Err("structured SHA proof/key binding".into());
    }
    let len = usize::try_from(u64::from_le_bytes(reader.take(8)?.try_into().unwrap()))
        .map_err(|_| "structured SHA proof length overflow")?;
    let inner = reader.take(len)?;
    if !reader.0.is_empty() {
        return Err("structured SHA proof trailing bytes".into());
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

/// Fresh-randomness proof of externally supplied, ordered 32-byte messages.
/// This includes witness construction/preprocessing and does not time an online
/// benchmark. Verification is left to an independent caller, as in indexed mode.
pub fn prove_messages(key: &VerifierKey, messages: &[[u8; 32]]) -> Result<Run, String> {
    if messages.len() != key.config().batch() {
        return Err("SHA message count does not match structured key".into());
    }
    let mut entropy = [0; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut entropy))
        .map_err(|error| format!("OS randomness: {error}"))?;
    Ok(prove_with_rng(key, messages, StdRng::from_seed(entropy)))
}

fn prove_with_rng(key: &VerifierKey, messages: &[[u8; 32]], rng: StdRng) -> Run {
    let digests: Vec<[u8; 32]> = messages
        .iter()
        .map(|message| Sha256::digest(message).into())
        .collect();
    sha_zk::prove_core_structured_messages(key.config(), messages, rng, &key.statement(&digests))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Field, L};

    #[test]
    fn mask_first_rejects_previous_canonical_layout_key() {
        let key = VerifierKey::new(8, 1, 16, 3).unwrap();
        let mut previous = encode_key(&key);
        previous[..8].copy_from_slice(b"KEYSHA01");
        let old_relation = Hasher::<H>::default().hash(&[b"structured-sha-relation", b"sha256-32b-canonical-zk-layout-v2-global-d-f2^256-blake3-beta2-salt32"]);
        previous[8..40].copy_from_slice(&old_relation);
        assert!(decode_key(&previous).is_err());
        // A new envelope must not admit an old relation identifier either.
        previous[..8].copy_from_slice(KEY_MAGIC);
        assert!(decode_key(&previous).is_err());
    }

    #[test]
    fn global_capacity_rejects_immediately_previous_layout_formats() {
        let key=VerifierKey::new(8,1,16,3).unwrap();
        let mut encoded=encode_key(&key);
        let previous=Hasher::<H>::default().hash(&[b"structured-sha-relation",b"sha256-32b-canonical-zk-layout-v3-global-d-mask-first-f2^256-blake3-beta2-salt32"]);
        encoded[8..40].copy_from_slice(&previous);
        assert!(decode_key(&encoded).is_err());
        encoded[..8].copy_from_slice(b"KEYSHA02");
        assert!(decode_key(&encoded).is_err());
        let run=prove_with_rng(&key,&[[0;32],[1;32]],StdRng::seed_from_u64(991));
        let mut proof=encode_proof(&key,&run.proof);
        proof[..8].copy_from_slice(b"B2SIMD03");
        assert!(decode_proof(&key,&proof).is_err());
    }

    #[test]
    fn canonical_key_and_bounded_parameters() {
        for n in [8, 16, 32, 64, 128, 256] {
            for batch in [8, 16, 32, 64, 128, 256] {
                if batch >= n / 4 {
                    validate_parameters(n, batch / (n / 4), 871, 4).unwrap();
                }
            }
        }
        for parameters in [
            (0, 1, 871, 4),
            (512, 1, 871, 4),
            (8, 0, 871, 4),
            (8, 3, 871, 4),
            (8, usize::MAX, 871, 4),
            (32, 64, 871, 4),
            (8, 4, usize::MAX, 4),
            (8, 4, 871, usize::MAX),
            (8, 1, 871, 4),
        ] {
            assert!(
                VerifierKey::new(parameters.0, parameters.1, parameters.2, parameters.3).is_err()
            );
        }
        let key = VerifierKey::new(8, 1, 16, 3).unwrap();
        let bytes = encode_key(&key);
        assert_eq!(bytes.len(), 72);
        assert_eq!(encode_key(&decode_key(&bytes).unwrap()), bytes);
        for end in [0, 7, 8, 39, 40, 71] {
            assert!(decode_key(&bytes[..end]).is_err());
        }
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(decode_key(&bad).is_err());
        for offset in [0, 8, 40, 48, 56, 64] {
            let mut bad = bytes.clone();
            bad[offset] ^= 1;
            assert!(decode_key(&bad).is_err(), "key byte {offset}");
        }
        let mut bad = bytes.clone();
        bad[40..48].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode_key(&bad).is_err());
        assert!(prove_messages(&key, &[[0; 32]]).is_err());
    }

    #[test]
    fn full_structured_sha_roundtrip_and_mutations() {
        let key = VerifierKey::new(8, 1, 16, 3).unwrap();
        let messages = [[0; 32], [1; 32]];
        let run = prove_with_rng(&key, &messages, StdRng::seed_from_u64(991));
        assert_eq!(
            run.digests,
            messages.map(|message| <[u8; 32]>::from(Sha256::digest(message)))
        );
        let bytes = encode_proof(&key, &run.proof);
        let proof = decode_proof(&key, &bytes).unwrap();
        verify(&key, &run.digests, &proof).unwrap();
        let mut previous_format = bytes.clone();
        previous_format[..8].copy_from_slice(b"B2SIMD02");
        assert!(decode_proof(&key, &previous_format).is_err());
        // Same mathematics with the old expanded evaluator, but the new statement.
        sha_zk::verify_with_statement(
            key.config(),
            &run.digests,
            &proof,
            &key.statement(&run.digests),
            MatrixEvaluation::Expanded,
        )
        .unwrap();
        // Inner serialization alone does not permit an old-domain proof downgrade.
        assert!(sha_zk::verify(key.config(), &run.digests, &proof).is_err());
        assert!(decode_proof(&key, &proof.to_bytes()).is_err());
        assert!(Proof::from_bytes(key.config(), &bytes).is_err());
        for offset in [0, 8, 40] {
            let mut bad = bytes.clone();
            bad[offset] ^= 1;
            assert!(decode_proof(&key, &bad).is_err(), "proof byte {offset}");
        }
        for end in [0, 7, 8, 39, 40, 47, 48, bytes.len() - 1] {
            assert!(decode_proof(&key, &bytes[..end]).is_err());
        }
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(decode_proof(&key, &bad).is_err());
        let mut reordered = run.digests.clone();
        reordered.swap(0, 1);
        assert!(verify(&key, &reordered, &proof).is_err());
        let mut modified = run.digests.clone();
        modified[0][0] ^= 1;
        assert!(verify(&key, &modified, &proof).is_err());
        assert!(verify(&key, &run.digests[..1], &proof).is_err());
        for mutation in 0..12 {
            let mut bad = proof.clone();
            match mutation {
                0 => bad.nonce[0] ^= 1,
                1 => bad.endpoints[0] += L::ONE,
                2 => bad.sc1[0][0] += L::ONE,
                3 => bad.sc2[0][0] += L::ONE,
                4 => bad.value += L::ONE,
                5 => bad.y2 += L::ONE,
                6 => bad.conversions[0][0] += L::ONE,
                7 => bad.g.h_omega += L::ONE,
                8 => bad.g.tails[0][0] += L::ONE,
                9 => bad.g.openings[0][0].values[0] += L::ONE,
                10 => bad.pcs.tails[0][0] += L::ONE,
                _ => bad.pcs.openings[0][0].values[0] += L::ONE,
            }
            assert!(
                verify(&key, &run.digests, &bad).is_err(),
                "mutation {mutation}"
            );
        }
        let other_key = VerifierKey::new(8, 4, 871, 4).unwrap();
        assert!(decode_proof(&other_key, &bytes).is_err());
        assert_ne!(
            key.statement(&run.digests),
            other_key.statement(&run.digests)
        );
    }

    #[test]
    fn formal_parameter_sha_roundtrip_with_multiple_groups() {
        // Local correctness only: formal query/tail parameters, G=2, and B=8.
        let key = VerifierKey::new(16, 2, 871, 4).unwrap();
        let verifier_key = decode_key(&encode_key(&key)).unwrap();
        let messages: Vec<[u8; 32]> = (0..8).map(|i| [i; 32]).collect();
        let run = prove_with_rng(&key, &messages, StdRng::seed_from_u64(0x464f524d414c));
        let expected: Vec<[u8; 32]> = messages
            .iter()
            .map(|message| Sha256::digest(message).into())
            .collect();
        assert_eq!(run.digests, expected);
        let proof = decode_proof(&verifier_key, &encode_proof(&key, &run.proof)).unwrap();
        verify(&verifier_key, &run.digests, &proof).unwrap();
        let mut reordered = run.digests.clone();
        reordered.swap(0, 1);
        assert!(verify(&verifier_key, &reordered, &proof).is_err());
        for mutation in 0..3 {
            let mut bad = proof.clone();
            match mutation {
                0 => bad.value += L::ONE,
                1 => bad.g.openings[0][0].values[0] += L::ONE,
                _ => bad.pcs.openings[0][0].values[0] += L::ONE,
            }
            assert!(
                verify(&verifier_key, &run.digests, &bad).is_err(),
                "formal mutation {mutation}"
            );
        }
    }

    #[test]
    fn rewrapped_valid_legacy_proof_is_rejected_by_structured_verifier() {
        let key = VerifierKey::new(8, 1, 16, 3).unwrap();
        let (legacy, matrix) = sha_zk::prove_core(
            key.config(),
            1234,
            StdRng::seed_from_u64(0x4c4547414359),
            None,
        );
        assert!(matrix.is_none());
        sha_zk::verify(key.config(), &legacy.digests, &legacy.proof).unwrap();
        // All syntax and key binding are valid: only the old FS domain differs.
        let rewrapped = encode_proof(&key, &legacy.proof);
        let decoded = decode_proof(&key, &rewrapped).unwrap();
        assert!(verify(&key, &legacy.digests, &decoded).is_err());
    }
}
