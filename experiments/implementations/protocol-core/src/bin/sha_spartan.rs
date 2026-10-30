//! Usage: sha_spartan <N> <groups> <gamma> <tau> <seed> <output-dir>
//! Or:    sha_spartan verify <N> <groups> <gamma> <tau> <output-dir>
use b2proto::sha_spartan::{self, Config, Proof};
use std::{fs, path::Path, time::Instant};

fn rss() -> f64 {
	fs::read_to_string("/proc/self/status")
		.ok()
		.and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(str::to_owned))
		.and_then(|l| l.split_whitespace().nth(1)?.parse::<f64>().ok())
		.map(|v| v / 1024.0)
		.unwrap_or(0.0)
}
fn main() {
	let args: Vec<_> = std::env::args().skip(1).collect();
	let verify_only = args.first().map(String::as_str) == Some("verify");
	let a = if verify_only { &args[1..] } else { &args[..] };
	assert_eq!(a.len(), if verify_only { 5 } else { 6 }, "see source usage");
	let parse = |i: usize| a[i].parse::<usize>().unwrap();
	let start = Instant::now();
	let cfg = Config::new(parse(0), parse(1), parse(2), parse(3));
	let setup_s = start.elapsed().as_secs_f64();
	let dir = Path::new(&a[if verify_only { 4 } else { 5 }]);
	if verify_only {
		let t = Instant::now();
		let raw = fs::read(dir.join("statement.bin")).expect("statement");
		assert_eq!(raw.len(), 32 * cfg.batch());
		let digests: Vec<[u8; 32]> = raw.chunks_exact(32).map(|b| b.try_into().unwrap()).collect();
		let proof = Proof::from_bytes(&cfg, &fs::read(dir.join("proof.bin")).expect("proof")).expect("parse");
		sha_spartan::verify(&cfg, &digests, &proof).expect("independent verification");
		println!(
			"{{\"proof_ok\":true,\"internal_hash\":\"blake3\",\"mode\":\"independent_process_verify\",\"setup_s\":{setup_s:.6},\"read_parse_verify_s\":{:.6}}}",
			t.elapsed().as_secs_f64()
		);
		return;
	}
	assert!(!dir.exists(), "refusing to overwrite a previous run");
	fs::create_dir_all(dir).unwrap();
	let seed = a[4].parse::<u64>().unwrap();
	let run = sha_spartan::prove(&cfg, seed);
	let t = &run.times;
	let artifact_start = Instant::now();
	let encoded = run.proof.to_bytes();
	fs::write(dir.join("proof.bin"), &encoded).unwrap();
	let statement: Vec<u8> = run.digests.iter().flatten().copied().collect();
	fs::write(dir.join("statement.bin"), &statement).unwrap();
	let serialize_write_s = artifact_start.elapsed().as_secs_f64();
	let s = |d: std::time::Duration| d.as_secs_f64();
	let party_times: Vec<_> = t
		.parties
		.iter()
		.map(|p| {
			format!(
				"{{\"sc1_col_s\":{:.6},\"sc1_slot_s\":{:.6},\"sc2_prep_s\":{:.6},\"sc2_s\":{:.6}}}",
				s(p.sc1_col),
				s(p.sc1_slot),
				s(p.sc2_prep),
				s(p.sc2)
			)
		})
		.collect();
	let residual = s(t.total - t.witness - t.piop_share - t.pcs_prepare - t.piop - t.pcs_open - t.verify);
	let(client,prep,agg,public)=sha_spartan::communication(&cfg,&run.proof);
 let json = format!(
		concat!(
			"{{\"schema\":1,\"mode\":\"nonzk_sequential_all_parties\",\"proof_ok\":true,\"internal_hash\":\"blake3\",\"N\":{},\"batch\":{},\"groups\":{},\"seed\":{},",
			"\"message_bytes\":32,\"private_bits\":{},\"constraints_unpadded\":{},\"constraints_padded\":{},\"witness_slots_per_copy\":{},\"nnz_per_copy\":{},",
			"\"ell\":{},\"gamma\":{},\"tau\":{},\"beta\":2,\"share_field_bits\":128,\"challenge_field_bits\":256,",
			"\"setup_s\":{:.6},\"witness_s\":{:.6},\"piop_share_s\":{:.6},\"pcs_prepare_s\":{:.6},\"piop_s\":{:.6},\"pcs_open_s\":{:.6},\"verify_s\":{:.6},\"residual_s\":{:.6},\"spine_total_s\":{:.6},",
			"\"pcs_prepare_random_subset_s\":{:.6},\"pcs_prepare_share_subset_s\":{:.6},\"piop_conversion_preprocess_subset_s\":{:.6},\"piop_conversion_online_subset_s\":{:.6},",
			"\"serialize_write_s\":{:.6},\"setup_spine_artifact_total_s\":{:.6},\"proof_bytes_literal\":{},\"peak_rss_mb\":{:.1},",
			"\"client_upload_payload_bytes\":{},\"ideal_preprocessing_payload_bytes\":{},\"party_aggregate_payload_bytes\":{},\"public_proof_payload_bytes\":{},\"total_logical_payload_bytes\":{},\"piop_zk\":false,\"secure_aggregation\":false,\"network_s\":null,\"zk_mask_s\":null,\"party_local_work\":[{}]}}"
		),
		cfg.ctx.n,
		cfg.batch(),
		cfg.groups,
		seed,
		cfg.circuit.private_len * cfg.batch(),
		cfg.circuit.constraint_len * cfg.batch(),
		cfg.circuit.base.m0() * cfg.batch(),
		cfg.circuit.base.n0(),
		cfg.circuit.nnz(),
		cfg.pcs.params.ell,
		cfg.pcs.params.gamma,
		cfg.pcs.params.tau,
		setup_s,
		s(t.witness),
		s(t.piop_share),
		s(t.pcs_prepare),
		s(t.piop),
		s(t.pcs_open),
		s(t.verify),
		residual,
		s(t.total),
		s(t.pcs_random),
		s(t.pcs_share),
		s(t.conversion_preprocess),
		s(t.conversion_online),
		serialize_write_s,
		setup_s + s(t.total) + serialize_write_s,
		encoded.len(),
		rss(),
  client,prep,agg,public,client+prep+agg+public,
		party_times.join(",")
	);
	fs::write(dir.join("metrics.json"), format!("{json}\n")).unwrap();
	println!("{json}");
}
