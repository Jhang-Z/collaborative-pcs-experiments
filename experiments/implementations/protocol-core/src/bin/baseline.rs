//! Single-machine FRI-Binius baseline on Binius64: commit to M bits packed into GHASH-128
//! elements, then open one multilinear evaluation by Ring Switching + BaseFold, and verify.
//!
//! Usage: baseline <log2 input bits> [log_inv_rate] [n_queries | 0 = Binius64 rule at 100 bits] [blake3]
//! Run with RAYON_NUM_THREADS=1 for single-threaded numbers.

use std::time::Instant;

use binius_compute::GlobalAllocator;
use binius_field::{Field, Ghash128b as B128, PackedGhash1x128b as P, Random};
use binius_hash::{Blake3HashSuite, HashSuite};
use binius_hash_prover::ParallelHashSuite;
use binius_iop::{
	basefold::compiler::BaseFoldVerifierCompiler,
	channel::{IOPVerifierChannel, OracleSpec},
	fri::{MinProofSizeStrategy, calculate_n_test_queries},
	merkle_tree::BinaryMerkleTreeScheme,
};
use binius_iop_prover::{basefold::compiler::BaseFoldProverCompiler, channel::IOPProverChannel};
use binius_math::{
	FieldBuffer,
	multilinear::eq::eq_ind_partial_eval,
	ntt::{NeighborsLastSingleThread, domain_context::GaoMateerOnTheFly},
};
use binius_transcript::{ProverTranscript, fiat_shamir::HasherChallenger};
use binius_verifier::ring_switch::{eval_rs_eq, verify as rs_verify};
use rand::{SeedableRng, rngs::StdRng};

fn main() {
	let hash = std::env::args().nth(4).unwrap_or_else(|| "blake3".into());
	match hash.as_str() {
		"blake3" => run::<Blake3HashSuite>(&hash),
		other => panic!("unknown hash {other}"),
	}
}

/// Commit, open and verify with Merkle trees and Fiat–Shamir both on the hash suite H.
fn run<H: ParallelHashSuite>(hash: &str)
where
	H::LeafHash: Default,
{
	type Challenger<H> = HasherChallenger<<H as HashSuite>::LeafHash>;
	let args: Vec<String> = std::env::args().collect();
	let log_bits: usize = args.get(1).map_or(24, |s| s.parse().unwrap());
	let log_inv_rate: usize = args.get(2).map_or(1, |s| s.parse().unwrap());
	let q_arg: usize = args.get(3).map_or(0, |s| s.parse().unwrap());
	let n_queries = if q_arg == 0 { calculate_n_test_queries(100, log_inv_rate) } else { q_arg };
	let n_vars = log_bits - 7; // 128 bits per GHASH element

	let mut rng = StdRng::seed_from_u64(1);
	let witness = FieldBuffer::<P>::new(n_vars, (0..1usize << n_vars).map(|_| P::random(&mut rng)).collect());
	let point: Vec<B128> = (0..log_bits).map(|_| B128::random(&mut rng)).collect();
	// The bit-level claim: evaluate the packed multilinear by ring switching's own definition.
	// We obtain it from the prover's partial evaluations (s_hat_v) via the verifier check below,
	// so here we compute it directly: B~(r) = Σ_v eq(r_lo)[v] · s_hat_v.
	let t0 = Instant::now();
	let verifier_compiler = BaseFoldVerifierCompiler::new(
		&BinaryMerkleTreeScheme::<B128, H>::new(),
		vec![OracleSpec::new(n_vars)],
		log_inv_rate,
		n_queries,
		&MinProofSizeStrategy,
	);
	let ntt = NeighborsLastSingleThread::new(GaoMateerOnTheFly::<B128>::generate(
		verifier_compiler.max_log_domain_size(),
	));
	let prover_compiler = BaseFoldProverCompiler::<P, _>::from_verifier_compiler(&verifier_compiler, ntt);
	let setup_s = t0.elapsed().as_secs_f64();

	// === Prover: commit + open ===
	let t1 = Instant::now();
	let mut transcript = ProverTranscript::new(Challenger::<H>::default());
	let mut channel = prover_compiler.create_channel_from_transcript::<H, Challenger<H>, _, _>(
		&mut transcript,
		StdRng::seed_from_u64(2),
		GlobalAllocator,
	);
	let oracle = channel.send_oracle(witness.clone());
	let commit_s = t1.elapsed().as_secs_f64();
	let t2 = Instant::now();
	let rs = binius_prover::ring_switch::prove(&GlobalAllocator, witness.as_view(), &point, &mut channel);
	let claim_for_basefold = rs.sumcheck_claim;
	channel.prove_oracle_relation(oracle, rs.rs_eq_ind.into(), claim_for_basefold);
	channel.finish();
	let open_s = t2.elapsed().as_secs_f64();
	let proof = transcript.finalize();

	// The evaluation claim B~(point), recomputed from the witness (not timed).
	let eval_claim = bit_level_eval(&witness, &point);

	// === Verifier ===
	let t3 = Instant::now();
	let mut vt = binius_transcript::VerifierTranscript::new(Challenger::<H>::default(), proof.clone());
	let mut vch = verifier_compiler.create_channel_from_transcript::<H, Challenger<H>, _>(&mut vt);
	let v_oracle = vch.recv_oracle(1 << n_vars, n_vars, false).unwrap();
	let rsv = rs_verify::<B128, _>(eval_claim, &point, &mut vch).expect("ring switch verifies");
	let (_, point_hi) = point.split_at(7);
	let point_hi = point_hi.to_vec();
	let eq_rpp = rsv.eq_r_double_prime.clone();
	vch.verify_oracle_relation(
		v_oracle,
		Box::new(move |q: &[B128]| eval_rs_eq(&point_hi, q, &eq_rpp)),
		rsv.sumcheck_claim,
	)
	.expect("basefold verifies");
	vch.finish().expect("verifier finishes");
	let verify_ms = t3.elapsed().as_secs_f64() * 1e3;

	println!(
		"{{\"scheme\":\"binius64-fri-binius\",\"hash\":\"{hash}\",\"log_bits\":{log_bits},\"log_inv_rate\":{log_inv_rate},\"n_queries\":{n_queries},\
\"commit_ms\":{:.1},\"open_ms\":{:.1},\"prove_ms\":{:.1},\"proof_bytes\":{},\"verify_ms\":{verify_ms:.1},\"setup_s\":{setup_s:.2}}}",
		commit_s * 1e3,
		open_s * 1e3,
		(commit_s + open_s) * 1e3,
		proof.len()
	);
}

/// B~(r) for the bit table packed into `witness`: bits are the low coordinates of r.
fn bit_level_eval(witness: &FieldBuffer<P>, point: &[B128]) -> B128 {
	use binius_field::{BinaryField1b as B1, ExtensionField};
	let (lo, hi) = point.split_at(7);
	let eq_hi = eq_ind_partial_eval::<B128>(hi);
	let eq_lo = eq_ind_partial_eval::<B128>(lo);
	let mut acc = B128::ZERO;
	for (i, w) in witness.iter_scalars().enumerate() {
		let mut inner = B128::ZERO;
		for (b, bit) in ExtensionField::<B1>::iter_bases(&w).enumerate() {
			if bit == B1::ONE {
				inner += eq_lo.as_ref()[b];
			}
		}
		acc += eq_hi.as_ref()[i] * inner;
	}
	acc
}
