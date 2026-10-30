//! Application identity is public and bound by each canonical verifier key.
use crate::{sha_structured, keccak_structured, sha_zk::{Config, Proof}};
use serde::{Deserialize, Serialize};
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Serialize, Deserialize, clap::ValueEnum)]
#[serde(rename_all = "lowercase")]
pub enum Application { #[default] Sha256, Keccak }
impl Application {
    pub fn input_bytes(self) -> usize { match self { Self::Sha256 => 32, Self::Keccak => 200 } }
}
pub enum StructuredKey { Sha(sha_structured::VerifierKey), Keccak(keccak_structured::VerifierKey) }
impl StructuredKey {
    pub fn new(app: Application, n: usize, groups: usize, gamma: usize, tau: usize) -> Result<Self, String> {
        match app { Application::Sha256 => sha_structured::VerifierKey::new(n,groups,gamma,tau).map(Self::Sha),
                    Application::Keccak => keccak_structured::VerifierKey::new(n,groups,gamma,tau).map(Self::Keccak) }
    }
    pub fn config(&self) -> &Config { match self { Self::Sha(k) => k.config(), Self::Keccak(k) => k.config() } }
    pub fn statement(&self, outputs: &[[u8;32]]) -> Vec<u8> { match self { Self::Sha(k) => k.statement(outputs), Self::Keccak(k) => k.statement(outputs) } }
    pub fn encode(&self) -> Vec<u8> { match self { Self::Sha(k) => sha_structured::encode_key(k), Self::Keccak(k) => keccak_structured::encode_key(k) } }
    pub fn decode(bytes: &[u8]) -> Result<Self,String> {
        if bytes.starts_with(b"KEYSHA03") { sha_structured::decode_key(bytes).map(Self::Sha) }
        else { keccak_structured::decode_key(bytes).map(Self::Keccak) }
    }
    pub fn encode_proof(&self, proof: &Proof) -> (Vec<u8>, &'static str) {
        match self { Self::Sha(k) => (sha_structured::encode_proof(k,proof),"B2SIMD04"), Self::Keccak(k) => (keccak_structured::encode_proof(k,proof),"B2KEC001") }
    }
    pub fn verify(&self, outputs: &[[u8;32]], bytes: &[u8]) -> Result<(),String> {
        match self { Self::Sha(k) => sha_structured::verify(k, outputs, &sha_structured::decode_proof(k,bytes)?),
                    Self::Keccak(k) => keccak_structured::verify(k, outputs, &keccak_structured::decode_proof(k,bytes)?) }
    }
}
