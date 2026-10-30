# Collaborative PCS and Keccak experiment artifact

Source and scripts for reproducing the four experiment groups of our collaborative multilinear PCS and binary-circuit PIOP. The runner builds the implementations, measures actual party computations, replays the same LAN/WAN model, verifies proofs where supported, and exports public measurements into one results bundle.

## Requirements

- **Linux x86_64**, Python **3.10+**, systemd and **cgroup v2** with the memory controller. Use a normal SSH login on a server; a minimal container without a systemd manager is insufficient.
- At least **two allowed logical CPUs**: one for measured computation and others for MPI progress/control. Pappas also requires **AVX2**. No GPU is needed.
- Internet access for fixed upstream sources, Rust crates and missing tools. Debian/Ubuntu support installation of missing system packages through `apt-get` (root or `sudo`); compatible installed tools are reused.
- Enough available RAM and storage for the chosen workload. The complete matrix has large Pappas cases using roughly **100–110 GiB** on the original host. These are observations, not guaranteed bounds for every machine. A small smoke run is the first check on a new server.
- A writable checkout and temporary storage, including writable `/dev/shm` for the unchanged Pappas PCS preparation boundary. Private prepared files are local run data, not part of the public bundle.

The memory limit is **not fixed at 256 GB or 110 GiB**. Before each case the runner reads `MemAvailable` and all visible ancestor-cgroup limits, takes the smallest available capacity, and leaves **10%** as a system reserve. Inside the actual service it checks the service ancestors again, reduces the limit if necessary, then verifies the enforced limit before any proof starts. It disables swap for the case. If a configuration reaches the limit or fails verification, the runner retains the failure and stops; it never shrinks the circuit or subtracts memory-reclaim time.

The **current confirmation focuses on Groups 1 and 4**. Groups 2 and 3 remain available as implementation paths, but their comparison settings are under discussion; including them does not endorse a finalized fair comparison.

## Quick start

Clone this repository, enter its directory, then inspect the environment without installing anything:

```bash
./reproduce.sh --check-env
```

Run a small correctness check for the currently selected Groups 1 and 4. This installs missing prerequisites, fetches pinned dependencies and builds fresh small proofs:

```bash
./reproduce.sh --groups 1 4 --smoke
```

Run Groups 1 and 4 once:

```bash
./reproduce.sh --groups 1 4
```

Every group can be selected separately with `--groups 1`, `--groups 2`, `--groups 3`, or `--groups 4`. Select several by listing them, for example `--groups 1 4`. Omitting `--groups` runs all four groups; Groups 2 and 3 currently retain the settings under discussion.

The first command that builds may ask `sudo` to install missing packages. Incompatible toolchains are installed in project-local directories. Existing system compiler defaults and the default Rust toolchain are not changed. Bootstrap and measurement logs are kept locally. Setup may take a while; full reproduction includes preprocessing and sequential execution of every logical worker and can take hours even when the simulated online time is seconds.

To reproduce only the four Keccak×4096 scaling points:

```bash
./reproduce.sh --groups 4 --instances 4096
```

Other useful commands:

```bash
# See the exact 74 unique proof jobs without building or running them.
./reproduce.sh --plan

# Only standalone PCS, or only the native Binius64 comparison.
./reproduce.sh --groups 2
./reproduce.sh --groups 1

# Reuse existing tools only; do not install prerequisites.
./reproduce.sh --groups 4 --instances 4096 --no-install

# Optional stricter policy: reserve 20% of currently available capacity.
./reproduce.sh --groups 4 --instances 4096 --reserve-fraction 0.20
```

`--memory-gib VALUE` can set a smaller explicit limit, but cannot exceed the detected safe budget. `--output /path/to/new-directory` selects a **new** run directory; existing runs are never overwritten. `--timeout-seconds` changes only the per-command watchdog (default 10800 seconds), not the protocol or reported online time. Do not run other heavy jobs during measurements.

## Outputs

Each invocation creates `runs/<UTC timestamp>/`:

| File/directory | Contents |
|---|---|
| `public/plan.json`, `operations.json` | Selected scientific configuration, unique proof jobs and operational choices |
| `public/results.csv` | One row per completed configuration/network: online time, compute critical path, communication increment and byte count, memory budget/peak, validation scope |
| `public/stages.csv` | Measured worker critical-path and coordinator time for each recorded exchange of our implementation |
| `public/results.json`, `report.md` | Machine-readable status and comparison tables; failures remain explicit |
| `public/resources/`, `cases/` | Per-case memory telemetry, limit/OOM/swap events, validation status |
| `public/traces/` | Timing and message-size metadata used for independent replay; no message payloads |
| `public/build-identity.json` | Actual tool versions, fixed dependency identities, source/binary identities |
| `results-public.tar.gz` | Unified public data bundle, including a SHA-256 file manifest |
| `private/` | Local inputs, shares, proofs, intermediate files and raw logs; **not exported** |

Copy **`results-public.tar.gz`** to share a run. Do not publish the entire run directory: private material and its hashes remain local. Run directories, dependency checkouts, builds and environment caches are excluded by `.gitignore`. Smoke runs are labelled `performance_sample=false` and are not paper measurements. Repeated samples, if explicitly configured, remain separate CSV rows. No figures are generated: send the public bundle back for plotting or analysis.

## Experiment configuration

[`configs/experiments.json`](configs/experiments.json) is the default scientific configuration:

| Group | Workload | Workers N | Baseline / network |
|---|---|---|---|
| 1 | Full 24-round Keccak-f[1600] ×512, ×1024 | 32, 64, 128, 256 | Native single-core Binius64; LAN |
| 2 | Standalone PCS, input bits M=2^16, 2^18, 2^20, 2^22, 2^24 | 32, 64, 128, 256 | Pappas PCS; LAN/WAN |
| 3 | Full Keccak-f ×32, ×64 | 16, 32, 64, 128 | Pappas native generation path; LAN/WAN |
| 4 | Our full Keccak-f ×512, ×1024, ×2048, ×4096 | 32, 64, 128, 256 | Scaling; LAN/WAN |

Each configuration has one completed sample. Groups 1 and 4 share identical proof jobs for ×512/1024, and a native single-core baseline is measured once per workload, giving **74 unique jobs**. This new reproduction generates fresh Keccak inputs and proof randomness; PCS uses the same deterministic shared test table across runs. Schemes receive the same input prefix and ordered public outputs within a run; exact numerical timings depend on the new hardware.

Keccak inputs are private 200-byte states; only the first 256 output bits are public. This is a batch of Keccak-f permutations, **not** the Keccak-256 sponge. Our parameters are gamma=871, tau=4. LAN is 10 Gbit/s with 2 ms RTT; WAN is 0.2 Gbit/s with 50 ms RTT. PCS schemes retain their native fields, padding and security parameters; equal input bits do not imply identical internal representations.

## How timing and validation work

Actual local computations execute sequentially, pinned to one measured CPU. Our round schedule waits for all required replies and therefore uses the slowest required worker, together with coordinator work. Pappas uses the instrumented MPI dependency graph. Both are replayed with `causal-fifo-tx-fair-rx-v1`, including message sizes, sender FIFO, receiver bandwidth sharing and causal dependencies. The coordinator and party 0 share one virtual CPU. We **do not divide total process wall time by N**. Native Binius64 is a direct single-core measurement with no simulated network charge.

Reported online time excludes preprocessing, initial sharing, file preparation, environment setup and verification according to each implementation's boundary. The bundle records `campaign_wall_s` from setup through the last case (before final archive export), completed `setup_and_inputs_wall_s`, each case's `execution_wall_s`, and separate prepare/prove/verify command wall times. These actual durations are distinct from the simulated online time. No reclaim duration or estimated cost is removed from an online interval. [`METHODS.md`](METHODS.md) describes the measured paths and offline preparation.

Our PCS/application proofs, Pappas PCS and native Binius64 undergo public verification, a corrupted-proof rejection check, and restored-proof acceptance. Keccak application outputs also match an independent Python Keccak oracle. **Pappas Keccak has only the author's native generation checks**; its rows explicitly set `full_proof_verified=false`. It has no independently implemented complete proof verifier in this artifact. Functional tests do not establish a new security theorem; the protocol uses the paper's stated ideal-functionality assumptions.

## Versions and source

Own implementation sources and measurement hooks are included. Binius64 and Pappas are downloaded at immutable commits and checked against file manifests before compilation. Rust is fixed in [`configs/toolchains.json`](configs/toolchains.json); compatible GNU C/C++, CMake and Open MPI are reused and their actual versions recorded. Pappas includes an upstream precompiled XKCP library; it is hash checked, not rebuilt from source. See [`THIRD_PARTY.md`](THIRD_PARTY.md) for provenance and license scope.

```bash
python3 scripts/verify_source.py
python3 -m unittest discover -s tests -v
```

The default configuration is intended for the paper comparison. For a different study, copy it and pass `--config /path/to/custom.json`; dimension checks in the actual implementations still apply. A larger memory budget does not remove Binius64's native wiring-address limit, so the default native comparison remains ×512/1024.

## Troubleshooting

- **No systemd user manager:** use a normal SSH login with a running user manager (`systemctl --user is-active default.target`). Root uses the system manager. The runner refuses an unenforced memory policy rather than silently running unbounded.
- **Insufficient RAM or a memory event:** inspect `public/cases/` and resource telemetry, including actual service-ancestor events. Free other jobs, use a larger host, or explicitly select a smaller experiment subset. The original failed run remains unchanged.
- **Missing packages without sudo access:** ask the administrator to install the packages named in the setup error, then rerun into a new directory. Other Linux distributions require manual system-package installation.
- **Build or command failure:** inspect `build/bootstrap.log` or the failed case's local private log. Fix the environment and start a new run; failures are never relabelled as successful samples.
- **Storage:** successful application share files are removed after verification; other local proof artifacts remain for inspection. Keep sufficient space for one large preparation and accumulated small proof outputs.
