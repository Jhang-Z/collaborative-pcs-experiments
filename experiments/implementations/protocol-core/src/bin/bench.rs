//! Runs one opening at the paper's parameters and prints a JSON line with per-party prover
//! times, proof size, and verifier time.
//!
//! Usage: bench <N> <log2 input bits> [blake3] [gamma] [tau]

use std::time::{Duration, Instant};

use b2proto::{
	params::{Params, ell_for_bits, input_bits},
	protocol::{Timings, proof_size, prove, rng_seed, verify},
	setup::{Setup, random_instance},
};
use binius_hash::{Blake3HashSuite, HashSuite};

fn ms(d: Duration) -> f64 {
	d.as_secs_f64() * 1e3
}

fn peak_rss_mb() -> f64 {
	std::fs::read_to_string("/proc/self/status")
		.ok()
		.and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.to_string()))
		.and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse::<f64>().ok()))
		.map(|kb| kb / 1024.0)
		.unwrap_or(0.0)
}

fn run<H: HashSuite>(np: usize, log_bits: usize, hash: &str, gamma: usize, tau: usize) {
	let beta = 2;
	let ell = ell_for_bits(np, gamma, tau, beta, 1usize << log_bits);
	let params = Params { n_parties: np, ell, beta, gamma, tau, salt_bytes: 32 };
	let t0 = Instant::now();
	let setup = Setup::new(params);
	let seed = rng_seed();
	let (inst, wit) = random_instance(&setup, seed, Some((1usize << log_bits) >> 8));
	let setup_s = t0.elapsed().as_secs_f64();

	let t1 = Instant::now();
	let (proof, times, client_share) = prove::<H>(&setup, &inst, &wit, seed);
	let prove_wall = t1.elapsed().as_secs_f64();
	let t2 = Instant::now();
	let queries = verify::<H>(&setup, &inst, &proof).expect("proof must verify");
	let verify_ms = ms(t2.elapsed());
	let size = proof_size(&setup, &proof, &queries);

	let mut totals: Vec<(Duration, usize)> = times.iter().enumerate().map(|(i, t)| (t.total(), i)).collect();
	totals.sort();
	let median = totals[totals.len() / 2].0;
	let (max, imax) = totals[totals.len() - 1];
	let phase = |t: &Timings| {
		format!(
			"{{\"share\":{:.2},\"encode\":{:.2},\"hash\":{:.2},\"frontend\":{:.2},\"weights\":{:.2},\"rounds\":{:.2}}}",
			ms(t.share), ms(t.encode), ms(t.hash), ms(t.frontend), ms(t.weights), ms(t.rounds)
		)
	};
	println!(
		"{{\"N\":{np},\"log_bits\":{log_bits},\"capacity_bits\":{},\"ell\":{ell},\"gamma\":{gamma},\"tau\":{tau},\"hash\":\"{hash}\",\
\"party_ms_median\":{:.2},\"party_ms_max\":{:.2},\"phases_max_party\":{},\"phases_median_party\":{},\
\"client_share_ms\":{:.2},\"proof_bytes\":{},\"proof_queries\":{},\"proof_tails\":{},\"proof_frontend\":{},\"verify_ms\":{verify_ms:.2},\
\"setup_s\":{setup_s:.1},\"prove_wall_s\":{prove_wall:.1},\"peak_rss_mb\":{:.0}}}",
		input_bits(&setup.layout),
		ms(median),
		ms(max),
		phase(&times[imax]),
		phase(&times[totals[totals.len() / 2].1]),
		ms(client_share),
		size.total,
		size.queries,
		size.tails,
		size.frontend,
		peak_rss_mb(),
	);
}

fn main() {
	let args: Vec<String> = std::env::args().collect();
	let np: usize = args.get(1).map_or(16, |s| s.parse().unwrap());
	let log_bits: usize = args.get(2).map_or(20, |s| s.parse().unwrap());
	let hash = args.get(3).map_or("blake3", |s| s.as_str()).to_string();
	let gamma: usize = args.get(4).map_or(871, |s| s.parse().unwrap());
	let tau: usize = args.get(5).map_or(4, |s| s.parse().unwrap());
	match hash.as_str() {
		"blake3" => run::<Blake3HashSuite>(np, log_bits, &hash, gamma, tau),
		other => panic!("unknown hash {other}"),
	}
}
