//! Prototype of the collaborative opening protocol of the paper
//! "Collaborative Polynomial Commitments for Bits: Distributed Ring Switching over a Shared
//! Binary Tensor Code", built on Binius64.

pub mod algebra;
pub mod code;
pub mod field;
pub mod fs;
pub mod merkle;
pub mod net;
pub mod net_simulation;
pub mod pcs_codec;
pub mod params;
pub mod protocol;
pub mod setup;
pub mod sharing;
pub mod spartan;
pub mod sha_circuit;
pub mod sha_spartan;

pub mod zk;

pub mod sha_zk;
pub mod sha_structured;

pub mod public_pcs;

pub mod sparse_matrix;

pub mod indexed;

pub mod indexed_codec;

pub mod parallel;
pub mod transport;

pub mod product_tree;

pub mod keccak_circuit;
pub mod keccak_structured;

pub mod field_pcs;
