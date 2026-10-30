//! Offline ideal dealer: write disjoint party shares, never an encoded private table.
use crate::{
    field::{B, D, Field, L, Random, from_words},
    setup::{Setup, Witness},
    sha_zk::Config,
    spartan::PartyShares,
    wire::{self, Reader},
    zk::{self, Selector},
};
use anyhow::{Result, ensure};
use rand::{SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{Read, Write},
    os::unix::fs::OpenOptionsExt,
    path::Path,
};

pub const LAYOUT_VERSION: u32 = 2;
#[derive(Clone, Serialize, Deserialize)]
pub struct Shape {
    #[serde(default)]
    pub layout_version: u32,
    #[serde(default)]
    pub application: crate::application::Application,
    pub parties: usize,
    pub messages: usize,
    pub gamma: usize,
    pub tau: usize,
    pub development: bool,
}
impl Shape {
    pub fn config(&self) -> Result<Config> {
        ensure!(self.layout_version == LAYOUT_VERSION, "prepared layout version; regenerate shares");
        ensure!(
            [8, 16, 32, 64, 128, 256].contains(&self.parties),
            "unsupported party count"
        );
        ensure!(
            self.messages % (self.parties / 4) == 0
                && (self.messages / (self.parties / 4)).is_power_of_two(),
            "message count/packing"
        );
        if self.development {
            ensure!(
                self.parties == 8 && self.messages == 2 && self.gamma >= 16 && self.tau == 3,
                "development shape"
            );
        } else {
            let max_messages = match self.application {
                crate::application::Application::Keccak => crate::keccak_structured::MAX_INSTANCES,
                crate::application::Application::Sha256 => 256,
            };
            ensure!(
                self.messages.is_power_of_two()
                    && (8..=max_messages).contains(&self.messages)
                    && self.gamma == 871
                    && self.tau == 4,
                "formal parameter shape"
            );
        }
        Ok(match self.application {
            crate::application::Application::Sha256 => Config::new(
                self.parties, self.messages / (self.parties / 4), self.gamma, self.tau),
            crate::application::Application::Keccak => Config::new_keccak(
            self.parties,
            self.messages / (self.parties / 4),
            self.gamma,
            self.tau,
        )})
    }
    pub fn read(out: &Path) -> Result<Self> {
        Ok(serde_json::from_slice(&fs::read(out.join("shape.json"))?)?)
    }
}
pub struct Shares {
    pub piop: PartyShares,
    pub masks: [Selector; 2],
    pub nonce: L,
    pub packed: [L; 2],
    pub ordinary: [Vec<L>; 2],
    pub main: Vec<L>,
    pub g: Vec<L>,
}
fn write_b(out: &mut Vec<u8>, v: &[B]) {
    out.extend((v.len() as u64).to_le_bytes());
    out.extend_from_slice(bytemuck::cast_slice(v));
}
fn read_b(r: &mut Reader<'_>) -> Result<Vec<B>> {
    let n = usize::try_from(r.u64()?)?;
    ensure!(n <= r.0.len() / 16, "B-vector length");
    Ok(r.take(n * 16)?
        .chunks_exact(16)
        .map(bytemuck::pod_read_unaligned)
        .collect())
}
// Prepared files are read once into private owned vectors before online timing.
// Retaining a second copy in the page cache can pressure a sequential simulator.
fn release_share_file_cache(file: &fs::File, written: bool) -> std::io::Result<()> {
    #[cfg(target_os = "linux")]
    {
        use std::os::fd::AsRawFd;
        unsafe extern "C" {
            fn posix_fadvise(fd: i32, offset: i64, len: i64, advice: i32) -> i32;
        }
        const POSIX_FADV_DONTNEED: i32 = 4;
        if written {
            file.sync_data()?;
        }
        let error = unsafe { posix_fadvise(file.as_raw_fd(), 0, 0, POSIX_FADV_DONTNEED) };
        if error != 0 {
            return Err(std::io::Error::from_raw_os_error(error));
        }
    }
    #[cfg(not(target_os = "linux"))]
    let _ = (file, written);
    Ok(())
}
impl Shares {
    pub fn write(&self, path: &Path) -> Result<()> {
        let mut b = b"B2SHR002".to_vec();
        write_b(&mut b, &self.piop.z);
        for row in &self.piop.rows {
            write_b(&mut b, row);
        }
        for m in &self.masks {
            b.extend((m.polys.len() as u64).to_le_bytes());
            for p in &m.polys {
                wire::fields(&mut b, p);
            }
        }
        wire::field(&mut b, self.nonce);
        for a in 0..2 {
            wire::field(&mut b, self.packed[a]);
            wire::fields(&mut b, &self.ordinary[a]);
        }
        wire::fields(&mut b, &self.main);
        wire::fields(&mut b, &self.g);
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)?;
        file.write_all(&b)?;
        release_share_file_cache(&file, true)?;
        Ok(())
    }
    pub fn read(path: &Path, cfg: &Config) -> Result<Self> {
        let mut file = fs::File::open(path)?;
        let mut b = Vec::with_capacity(usize::try_from(file.metadata()?.len())?);
        file.read_to_end(&mut b)?;
        release_share_file_cache(&file, false)?;
        let mut r = Reader(&b);
        ensure!(r.take(8)? == b"B2SHR002", "share file magic");
        let z = read_b(&mut r)?;
        let rows = [read_b(&mut r)?, read_b(&mut r)?, read_b(&mut r)?];
        ensure!(
            z.len() == cfg.circuit.base.n0() * cfg.groups
                && rows
                    .iter()
                    .all(|v| v.len() == cfg.circuit.base.m0() * cfg.groups),
            "PIOP share shape"
        );
        let mut masks = Vec::new();
        for (len, degree) in [(cfg.sc1_len(), 4), (cfg.sc2_len(), 3)] {
            ensure!(r.u64()? as usize == len, "mask dimension");
            let mut polys = Vec::new();
            for _ in 0..len {
                let p = r.fields()?;
                ensure!(p.len() == degree, "mask degree");
                polys.push(p);
            }
            masks.push(Selector { polys });
        }
        let nonce = r.field()?;
        let mut packed = [L::ZERO; 2];
        let mut ordinary = [vec![], vec![]];
        for a in 0..2 {
            packed[a] = r.field()?;
            ordinary[a] = r.fields()?;
            ensure!(ordinary[a].len() == cfg.ctx.k, "dsh shape");
        }
        let main = r.fields()?;
        let g = r.fields()?;
        ensure!(
            main.len() == cfg.pcs.params.n() && g.len() == cfg.g.params.n(),
            "PCS share shape"
        );
        r.finish()?;
        Ok(Self {
            piop: PartyShares { z, rows },
            masks: masks.try_into().ok().unwrap(),
            nonce,
            packed,
            ordinary,
            main,
            g,
        })
    }
}
pub fn entropy() -> Result<StdRng> {
    let mut seed = [0; 32];
    fs::File::open("/dev/urandom")?.read_exact(&mut seed)?;
    Ok(StdRng::from_seed(seed))
}
fn share_table(setup: &Setup, w: &Witness, rng: &mut StdRng) -> Vec<Vec<L>> {
    let n = setup.params.n();
    let k = setup.params.k();
    let mut rows = vec![vec![L::ZERO; n]; setup.params.n_parties];
    for x in 0..n {
        let sh = if setup.layout.is_pad[x] {
            setup.sharing.random_shares(rng)
        } else {
            setup
                .sharing
                .share(&(0..k).map(|y| w.get(n, y, x)).collect::<Vec<_>>(), rng)
        };
        for (i, v) in sh.into_iter().enumerate() {
            rows[i][x] = v;
        }
    }
    rows
}
pub fn run(shape: Shape, input: &Path, out: &Path) -> Result<()> {
    ensure!(!out.exists(), "use a fresh preparation directory");
    let start = std::time::Instant::now();
    let cfg = shape.config()?;
    let mut rng = entropy()?;
    let data = fs::read(input)?;
    let input_bytes = shape.application.input_bytes();
    ensure!(data.len() >= shape.messages * input_bytes, "input length");
    let copies: Vec<_> = data[..shape.messages * input_bytes]
        .chunks_exact(input_bytes)
        .map(|m| {
            let mut w = cfg.circuit.witness(m);
            cfg.circuit.randomize_masks(&mut w.0, &mut w.1, &mut rng);
            match shape.application {
                crate::application::Application::Sha256 => assert_eq!(w.2.as_slice(), Sha256::digest(m).as_slice()),
                crate::application::Application::Keccak => assert_eq!(w.2.as_slice(), &crate::keccak_circuit::reference(m.try_into().unwrap())[..32]),
            }
            w
        })
        .collect();
    let (n, k, n0, m0, g) = (
        cfg.ctx.n,
        cfg.ctx.k,
        cfg.circuit.base.n0(),
        cfg.circuit.base.m0(),
        cfg.groups,
    );
    let selectors = [
        Selector::random(cfg.sc1_len(), 3, &mut rng),
        Selector::random(cfg.sc2_len(), 2, &mut rng),
    ];
    let coefficients: Vec<_> = selectors.iter().flat_map(Selector::coefficients).collect();
    let gw = zk::g_witness(&cfg.g, &cfg.gmap, &coefficients);
    let grows = share_table(&cfg.g, &gw, &mut rng);
    let mut states: Vec<_> = grows
        .into_iter()
        .map(|gr| Shares {
            piop: PartyShares {
                z: vec![B::ZERO; n0 * g],
                rows: std::array::from_fn(|_| vec![B::ZERO; m0 * g]),
            },
            masks: [
                Selector {
                    polys: vec![vec![L::ZERO; 4]; cfg.sc1_len()],
                },
                Selector {
                    polys: vec![vec![L::ZERO; 3]; cfg.sc2_len()],
                },
            ],
            nonce: L::ZERO,
            packed: [L::ZERO; 2],
            ordinary: [vec![L::ZERO; k], vec![L::ZERO; k]],
            main: vec![],
            g: gr,
        })
        .collect();
    for a in 0..2 {
        for j in 0..selectors[a].polys.len() {
            for u in 0..selectors[a].polys[j].len() {
                let shares = cfg.ctx.share_sss(selectors[a].polys[j][u], &mut rng);
                for i in 0..n {
                    states[i].masks[a].polys[j][u] = shares[i];
                }
            }
        }
    }
    let nonce = L::random(&mut rng);
    for (i, v) in cfg.ctx.share_sss(nonce, &mut rng).into_iter().enumerate() {
        states[i].nonce = v;
    }
    for a in 0..2 {
        let r: Vec<_> = (0..k).map(|_| L::random(&mut rng)).collect();
        for (i, v) in cfg.ctx.share_packed(&r, &mut rng).into_iter().enumerate() {
            states[i].packed[a] = v;
        }
        for (y, &v) in r.iter().enumerate() {
            for (i, s) in cfg.ctx.share_sss(v, &mut rng).into_iter().enumerate() {
                states[i].ordinary[a][y] = s;
            }
        }
    }
    let mut buf = vec![B::ZERO; n];
    for gg in 0..g {
        for p in 0..cfg.circuit.private_len {
            cfg.ctx
                .share_bits(|y| copies[gg + g * y].0[p], &mut rng, &mut buf);
            for i in 0..n {
                states[i].piop.z[p + n0 * gg] = buf[i];
            }
        }
        for a in 0..3 {
            for j in 0..m0 {
                cfg.ctx
                    .share_bits(|y| copies[gg + g * y].1[a][j], &mut rng, &mut buf);
                for i in 0..n {
                    states[i].piop.rows[a][j + m0 * gg] = buf[i];
                }
            }
        }
    }
    let cols = cfg.pcs.params.n();
    let mut packed = vec![[0u128; 2]; k * cols];
    for y in 0..k {
        for gg in 0..g {
            for p in 0..cfg.circuit.private_len {
                if copies[gg + g * y].0[p] {
                    let a = cfg.map[p + n0 * gg];
                    let (h, x) = (a % D, a / D);
                    packed[y * cols + x][h / 128] |= 1u128 << (h % 128);
                }
            }
        }
    }
    let mut w = Witness {
        table: packed.into_iter().map(from_words).collect(),
    };
    for m in cfg.pcs.layout.masks.iter().flatten() {
        w.table[m.y * cols + m.x] = L::random(&mut rng);
    }
    for (s, row) in states.iter_mut().zip(share_table(&cfg.pcs, &w, &mut rng)) {
        s.main = row;
    }
    fs::create_dir(out)?;
    fs::write(out.join("shape.json"), serde_json::to_vec_pretty(&shape)?)?;
    fs::write(
        out.join("statement.bin"),
        copies.iter().flat_map(|w| w.2).collect::<Vec<_>>(),
    )?;
    for (i, s) in states.into_iter().enumerate() {
        s.write(&out.join(format!("party-{i}.private")))?;
    }
    fs::write(
        out.join("preparation.json"),
        serde_json::to_vec_pretty(
            &serde_json::json!({"phase":"offline_ideal_dealer","seconds":start.elapsed().as_secs_f64(),"witness_encoding_started":false,"private_material_fresh_os_entropy":true,"development":shape.development,"input_sha256":Sha256::digest(&data[..shape.messages*input_bytes]).iter().map(|b|format!("{b:02x}")).collect::<String>()}),
        )?,
    )?;
    Ok(())
}

#[cfg(test)]
mod layout_version_tests {
    use super::*;
    #[test]
    fn exact_sha_compatibility_input_prepares_without_overread() {
        let root = std::env::temp_dir().join(format!("cube-prepare-sha-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&root).unwrap();
        let input = root.join("input");
        let bytes = [7u8; 64];
        fs::write(&input, bytes).unwrap();
        let out = root.join("prepared");
        run(Shape { layout_version: LAYOUT_VERSION, application: crate::application::Application::Sha256,
            parties:8, messages:2, gamma:16, tau:3, development:true }, &input, &out).unwrap();
        assert_eq!(fs::read(out.join("statement.bin")).unwrap(), Sha256::digest(&bytes[..32]).repeat(2));
        assert!(out.join("preparation.json").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn old_prepared_layout_is_rejected_and_applications_are_explicit() {
        let old = r#"{"parties":8,"messages":2,"gamma":16,"tau":3,"development":true}"#;
        let mut shape: Shape = serde_json::from_str(old).unwrap();
        assert!(shape.config().is_err());
        shape.layout_version = LAYOUT_VERSION;
        assert!(!shape.config().unwrap().circuit.keccak);
        shape.application = crate::application::Application::Keccak;
        assert!(shape.config().unwrap().circuit.keccak);
    }
}
