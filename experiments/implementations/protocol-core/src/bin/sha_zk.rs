//! sha_zk [verify] N groups gamma tau [input-seed] output-dir
use b2proto::{
    field::D,
    sha_zk::{self, Config, Proof},
};
use std::{fs, path::Path, time::Instant};
fn s(d: std::time::Duration) -> f64 {
    d.as_secs_f64()
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let verify = args.first().map(String::as_str) == Some("verify");
    let a = if verify { &args[1..] } else { &args[..] };
    assert_eq!(a.len(), if verify { 5 } else { 6 });
    let wall = Instant::now();
    let cfg = Config::new(
        a[0].parse().unwrap(),
        a[1].parse().unwrap(),
        a[2].parse().unwrap(),
        a[3].parse().unwrap(),
    );
    let setup_s = s(wall.elapsed());
    let dir = Path::new(&a[if verify { 4 } else { 5 }]);
    if verify {
        let t = Instant::now();
        let b = fs::read(dir.join("statement.bin")).unwrap();
        assert_eq!(b.len(), 32 * cfg.batch());
        let d: Vec<_> = b.chunks_exact(32).map(|b| b.try_into().unwrap()).collect();
        let p = Proof::from_bytes(&cfg, &fs::read(dir.join("proof.bin")).unwrap()).unwrap();
        sha_zk::verify(&cfg, &d, &p).unwrap();
        println!(
            "{{\"proof_ok\":true,\"internal_hash\":\"blake3\",\"setup_s\":{setup_s},\"read_parse_verify_s\":{}}}",
            s(t.elapsed())
        );
        return;
    }
    assert!(!dir.exists());
    fs::create_dir_all(dir).unwrap();
    let seed = a[4].parse().unwrap();
    let run = sha_zk::prove(&cfg, seed);
    let t = &run.times;
    let serial = Instant::now();
    let b = run.proof.to_bytes();
    fs::write(dir.join("proof.bin"), &b).unwrap();
    fs::write(
        dir.join("statement.bin"),
        run.digests.iter().flatten().copied().collect::<Vec<u8>>(),
    )
    .unwrap();
    let serialize_write_s = s(serial.elapsed());
    let (client, prep, agg, proof) = sha_zk::communication(&cfg, &run.proof);
    let gbytes = {
        let p = &run.proof.g;
        32 * (p.roots.len()
            + 1
            + 1
            + 1
            + 2 * p.coeffs.len()
            + p.tails.iter().map(Vec::len).sum::<usize>()
            + p.tail_salts.len()
            + p.openings
                .iter()
                .flatten()
                .map(|o| 3 + o.path.len())
                .sum::<usize>())
    };
    let json = format!(
        concat!(
            "{{\"schema\":5,\"mode\":\"v04_zk_ideal_sequential\",\"proof_ok\":true,\"internal_hash\":\"blake3\",\"N\":{},\"groups\":{},\"batch\":{},\"input_seed\":{},\"proof_coins\":\"fresh_OS_256bit\",\"kappa\":10,",
            "\"private_bits\":{},\"constraints_unpadded\":{},\"constraints_padded\":{},\"ell\":{},\"g_ell\":{},\"gamma\":{},\"tau\":{},\"coefficient_count\":{},\"setup_s\":{},\"witness_s\":{},\"piop_share_s\":{},\"mask_coefficient_share_s\":{},\"nonce_s\":{},",
            "\"pcs_prepare_s\":{},\"g_prepare_s\":{},\"piop_s\":{},\"g_open_s\":{},\"pcs_open_s\":{},\"verify_s\":{},\"spine_total_s\":{},\"prover_all_parties_s\":{},\"serialize_write_s\":{},\"setup_spine_artifact_total_s\":{},",
            "\"conversion_preprocess_subset_s\":{},\"conversion_online_subset_s\":{},\"proof_bytes_literal\":{},\"g_proof_bytes_literal\":{},\"client_upload_payload_bytes\":{},\"ideal_preprocessing_payload_bytes\":{},\"party_aggregate_payload_bytes\":{},\"public_proof_payload_bytes\":{},\"total_logical_payload_bytes\":{},",
            "\"aggregation\":\"ideal_plaintext\",\"network_s\":null,\"socket_bytes\":null,\"field_bytes\":{},\"bit_share_bytes\":16}}"
        ),
        cfg.ctx.n,
        cfg.groups,
        cfg.batch(),
        seed,
        cfg.circuit.private_len * cfg.batch(),
        cfg.circuit.constraint_len * cfg.batch(),
        cfg.circuit.base.m0() * cfg.batch(),
        cfg.pcs.params.ell,
        cfg.g.params.ell,
        cfg.pcs.params.gamma,
        cfg.pcs.params.tau,
        cfg.gmap.len(),
        setup_s,
        s(t.witness),
        s(t.piop_share),
        s(t.mask),
        s(t.nonce),
        s(t.pcs_prepare),
        s(t.g_prepare),
        s(t.piop),
        s(t.g_open),
        s(t.pcs_open),
        s(t.verify),
        s(t.total),
        s(t.total - t.verify),
        serialize_write_s,
        setup_s + s(t.total) + serialize_write_s,
        s(t.conversion_preprocess),
        s(t.conversion_online),
        b.len(),
        gbytes,
        client,
        prep,
        agg,
        proof,
        client + prep + agg + proof,
        D / 8
    );
    fs::write(dir.join("metrics.json"), format!("{json}\n")).unwrap();
    println!("{json}");
}
