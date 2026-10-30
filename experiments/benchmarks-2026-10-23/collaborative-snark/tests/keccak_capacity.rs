use ours_fullnet::{application::{Application, StructuredKey}, field::{B, D}, prepare::{Shape, LAYOUT_VERSION}};

fn shape(n: usize, messages: usize) -> Shape {
    Shape { layout_version: LAYOUT_VERSION, application: Application::Keccak,
        parties: n, messages, gamma: 871, tau: 4, development: false }
}

#[test]
fn invalid_keccak_capacity_rejects_before_layout_allocation() {
    for n in [32, 64, 128, 256] {
        for messages in [0, 4095, 4097, 8192, usize::MAX] {
            assert!(shape(n, messages).config().is_err());
        }
    }
    let mut sha = shape(32, 4096);
    sha.application = Application::Sha256;
    assert!(sha.config().is_err());
}

#[test]
#[ignore = "explicit public-only 4096 geometry check; allocates large address maps, no private shares/proof"]
fn keccak_maximum_public_geometry_and_key_roundtrip() {
    for n in [32, 64, 128, 256] {
        let cfg = shape(n, 4096).config().unwrap();
        assert_eq!(cfg.batch(), 4096);
        assert_eq!(cfg.groups, 4096 / (n / 4));
        assert!(cfg.circuit.keccak);
        let columns = cfg.pcs.params.n();
        let mut theta = vec![false; columns];
        for mask in cfg.pcs.layout.masks.iter().flatten() { theta[mask.x] = true; }
        let mut used = vec![false; columns];
        for chunk in cfg.map.chunks(D) {
            let x = chunk[0] / D;
            assert!(!used[x] && !theta[x] && !cfg.pcs.layout.is_pad[x]);
            used[x] = true;
            for (h, &address) in chunk.iter().enumerate() { assert_eq!(address, x * D + h); }
        }
        let start = cfg.circuit.mask_start.unwrap().0;
        let mut common_axes = None;
        for group in 0..cfg.groups {
            for block in 0..4 {
                let at = group * cfg.circuit.base.n0() + start + 1024 * block;
                let c: Vec<_> = (0..4).map(|j| cfg.map[at + j * D] / D).collect();
                let (a, b) = (c[0] ^ c[1], c[0] ^ c[2]);
                assert!(a.is_power_of_two() && b.is_power_of_two() && a != b);
                assert_eq!(c[0] & (a | b), 0);
                assert_eq!(c[3], c[0] ^ a ^ b);
                assert_eq!(*common_axes.get_or_insert((a, b)), (a, b));
                for j in 0..1024 { assert_eq!(cfg.map[at + j], c[j / D] * D + j % D); }
            }
        }
        assert_eq!(cfg.gmap.len(), 4 * cfg.sc1_len() + 3 * cfg.sc2_len());
        let mut g_used = std::collections::HashSet::new();
        for &cell in &cfg.gmap {
            let (y, x) = (cell / cfg.g.params.n(), cell % cfg.g.params.n());
            assert!(g_used.insert(cell) && y < cfg.g.params.k() && !cfg.g.layout.is_pad[x]);
            assert!(!cfg.g.layout.masks.iter().flatten().any(|m| m.y == y && m.x == x));
        }
        let share_bytes = n as u128 * cfg.groups as u128
            * (cfg.circuit.base.n0() + 3 * cfg.circuit.base.m0()) as u128
            * std::mem::size_of::<B>() as u128;
        println!("{{\"instances\":4096,\"N\":{n},\"groups\":{},\"columns\":{columns},\"SC1\":{},\"SC2\":{},\"minimum_piop_share_storage_bytes\":{share_bytes},\"public_geometry_passed\":true,\"full_proof_run\":false}}",
            cfg.groups, cfg.sc1_len(), cfg.sc2_len());
        drop(cfg);
    }
    // The current maximum must survive the canonical-key codec as well as prepare.
    let key = StructuredKey::new(Application::Keccak, 32, 512, 871, 4).unwrap();
    let bytes = key.encode();
    assert_eq!(&bytes[..8], b"KEYKEC01");
    drop(key);
    let decoded = StructuredKey::decode(&bytes).unwrap();
    assert_eq!(decoded.config().batch(), 4096);
    assert_eq!(decoded.encode(), bytes);
}
