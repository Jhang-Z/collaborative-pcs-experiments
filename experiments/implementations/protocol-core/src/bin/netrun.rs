//! Networked run: one aggregator and N party processes on this machine, over TCP.
//!
//! Usage:
//!   netrun local <N> <log2 input bits> [port] [label]   # spawns client and servers, prints a JSON line
//!   netrun party <id> <N> <log2 input bits> <seed> <addr>
//!   netrun client <N> <log2 input bits> <seed> <addr>
//!
//! Network conditions are applied outside the program (e.g. `tc qdisc ... netem` on lo).
//! The hash suite is chosen by the environment variable B2_HASH (blake3 only; defaults to blake3).

use std::{net::TcpListener, process::Command};

use b2proto::{
	net::{run_aggregator, run_client, run_party},
	params::{Params, ell_for_bits},
	protocol::rng_seed,
	setup::Setup,
};
use binius_hash::{Blake3HashSuite};

fn setup_for(np: usize, log_bits: usize) -> Setup {
	let (gamma, tau, beta) = (871, 4, 2);
	let ell = ell_for_bits(np, gamma, tau, beta, 1usize << log_bits);
	Setup::new(Params { n_parties: np, ell, beta, gamma, tau, salt_bytes: 32 })
}

fn hash() -> String {
	std::env::var("B2_HASH").unwrap_or_else(|_| "blake3".into())
}

fn main() {
	let a: Vec<String> = std::env::args().collect();
	match a[1].as_str() {
		"party" => {
			let (id, np, lb, seed) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap());
			let setup = setup_for(np, lb);
			match hash().as_str() {
				"blake3" => run_party::<Blake3HashSuite>(&setup, id, seed, &a[6]),
				other => panic!("unsupported internal hash {other}; use blake3"),
			}
		}
		"client" => {
			let (np, lb, seed): (usize, usize, u64) = (a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap());
			let setup = setup_for(np, lb);
			run_client(&setup, seed, Some((1usize << lb) >> 8), &a[5]);
		}
		"local" => {
			let np: usize = a[2].parse().unwrap();
			let lb: usize = a[3].parse().unwrap();
			let port: u16 = a.get(4).map_or(47000, |s| s.parse().unwrap());
			let label = a.get(5).cloned().unwrap_or_default();
			let addr = format!("127.0.0.1:{port}");
			let listener = TcpListener::bind(&addr).unwrap();
			let seed = rng_seed();
			let exe = std::env::current_exe().unwrap();
			let children: Vec<_> = (0..np)
				.map(|i| {
					// One core per party: keep Binius64's internal rayon pool single-threaded and,
					// when PIN_CORES is set, pin party i to logical CPU (i mod PIN_CORES) + 1.
					let mut cmd = match std::env::var("PIN_CORES").ok().and_then(|v| v.parse::<usize>().ok()) {
						Some(c) => {
							let mut t = Command::new("taskset");
							t.args(["-c", &(1 + i % c).to_string()]).arg(&exe);
							t
						}
						None => Command::new(&exe),
					};
					cmd.env("RAYON_NUM_THREADS", "1")
						.args(["party", &i.to_string(), &np.to_string(), &lb.to_string(), &seed.to_string(), &addr])
						.spawn()
						.unwrap()
				})
				.collect();
			// The input client runs on core 0 with the aggregator; it only shares and leaves.
			let client = Command::new(&exe)
				.env("RAYON_NUM_THREADS", "1")
				.args(["client", &np.to_string(), &lb.to_string(), &seed.to_string(), &addr])
				.spawn()
				.unwrap();
			let setup = setup_for(np, lb);
			let rep = match hash().as_str() {
				"blake3" => run_aggregator::<Blake3HashSuite>(&setup, seed, listener),
				other => panic!("unsupported internal hash {other}; use blake3"),
			};
			for mut c in children.into_iter().chain([client]) {
				c.wait().unwrap();
			}
			let ms = |d: std::time::Duration| d.as_secs_f64() * 1e3;
			let max_sent = rep.party_bytes.iter().map(|b| b.0).max().unwrap();
			let max_recv = rep.party_bytes.iter().map(|b| b.1).max().unwrap();
			let tot: u64 = rep.party_bytes.iter().map(|b| b.0 + b.1).sum();
			let compute: Vec<u64> = rep.party_compute_us.iter().map(|c| c.iter().sum()).collect();
			let max_compute = *compute.iter().max().unwrap() as f64 / 1e3;
			let phase_max: Vec<String> = (0..6)
				.map(|i| format!("{:.1}", rep.party_compute_us.iter().map(|c| c[i]).max().unwrap() as f64 / 1e3))
				.collect();
			println!(
				"{{\"label\":\"{label}\",\"hash\":\"{}\",\"N\":{np},\"log_bits\":{lb},\"ell\":{},\"total_ms\":{:.1},\"sharing_ms\":{:.1},\
\"commit_frontend_ms\":{:.1},\"folding_ms\":{:.1},\"termination_ms\":{:.1},\"max_party_compute_ms\":{max_compute:.1},\"phase_max_ms\":[{}],\
\"client_share_ms\":{:.1},\"client_sent_bytes\":{},\"max_party_sent_bytes\":{max_sent},\"max_party_recv_bytes\":{max_recv},\"total_party_bytes\":{tot},\"online_bytes\":{},\"proof_bytes\":{},\"verify_ms\":{:.1},\"proof_ok\":{}}}",
				hash(),
				setup.params.ell,
				ms(rep.total),
				ms(rep.sharing),
				ms(rep.commit_frontend),
				ms(rep.folding),
				ms(rep.termination),
				phase_max.join(","),
				ms(rep.client_share),
				rep.client_sent,
				rep.online_bytes,
				rep.proof_bytes,
				ms(rep.verify),
				rep.proof_ok
			);
		}
		m => panic!("unknown mode {m}"),
	}
}
