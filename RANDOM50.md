# Random XOR/AND general circuits

This entry packages the current general implementation: GENKEY05/GENPRF05, six-column public-input authentication, and private matrix authentication with 3-bit one-hot index blocks, two sumchecks and one binary PCS opening. Parameters are gamma=520 and tau=4. The main binary PCS is shared with the other adapters. This is a research implementation; the updated outer authentication and its costs must not be equated with every bound or historical performance table in the manuscript.

## Run

The Linux/systemd/cgroup requirements and automatic resource budget in [README.md](README.md) apply. First inspect and run a small correctness sample:

```bash
./reproduce.sh --config configs/random50.json --check-env
./reproduce.sh --config configs/random50.json --smoke
```

Smoke uses C=1024 and N=16 for both collaborative schemes, plus one single-core Binius64 run. It generates fresh proofs and is labelled `performance_sample=false`.

```bash
# Six candidate sizes, without builds or proof execution:
./reproduce.sh --config configs/random50.json --plan

# One chosen size, all N and its single-core baseline:
./reproduce.sh --config configs/random50.json --instances 1048576

# All six candidate sizes:
./reproduce.sh --config configs/random50.json
```

The configuration selects C=2^16 through 2^21, each at N=16,32,64,128: 24 Ours/Pappas pairs and six Binius64 jobs, **54 proof jobs** in total. These are candidate sizes, not a claim that a new machine has completed six sizes. A size counts as a completed comparison only when both schemes pass all four N values. Binius64 is measured once per C and repetition and does not determine the Ours/Pappas count. To examine other sizes, copy the JSON and change its `instances` list; C always means the original number of two-input computational gates. This public runner executes the selected finite matrix; it does not implement the private monitor's adaptive search for six successful sizes.

Unlike the legacy campaign, this entry attempts subsequent selected cases after an individual failure. All failures remain in `public/results.json` and `cases/`; failed cases have no successful timing row. `complete=true` means every selected job was attempted, while `all_passed` distinguishes successful completion. The command exits nonzero if any case failed. It does not silently reduce C/N, change parameters, retry failed proofs, or extrapolate results.

## Task and comparison contract

There are C/16 Boolean inputs. Seed 42 selects a dependency-valid wiring and a Bernoulli(1/2) choice of XOR or AND for each gate; actual counts need not be exactly half. Output is the final gate bit. The graph's logical gates and one fresh input are shared across schemes and N within a repetition; each N uses its natural layout, not a larger reserved capacity. The runner independently evaluates every Boolean gate before proving. Padding and native field representations remain scheme-specific.

Pappas uses S=1−2b to represent bits, with Boolean constraints on inputs and the signed-field XOR/AND relation. The patched native general frontend, compact static/auxiliary layouts, index binding, Merkle second-child fix and phase hooks are reconstructed from the pinned upstream commit with `third_party/pappas-general.patch`. Hashes are checked against the frozen general source. It retains native parameters and arithmetic. Its proof-size and verification-time numbers are **native internal statistics**; its full proof is not exported and independently verified. `full_proof_verified=false` records that boundary.

Ours is verified in a separate directory containing only the proof, verifier key and public statement. Mutated proof and wrong public output must be rejected. Binius64 uses `preserved-graph`, one thread, `--single`, and its native parameters; its separate public verification checks both negative cases as well. Neither comparison is a claim of identical internal security parameters. The gamma520 budget records the approximately 100-bit per-round knowledge convention and separately reports the accumulated interactive bound; it is not a final Fiat–Shamir security certificate.

The pinned preserved-graph Binius64 adapter failed at C=2^21 in the original campaign because its wiring address needed 65 bits while that path allows at most 63. This is a task/encoding-specific failure, not a universal Binius64 size limit. Failed runs must not be replaced by extrapolated times. Likewise, the original C=2^24 Ours attempt was excluded because the first index-encoding layer alone has a 128 GiB lower bound, above that host's 110 GiB budget. These observations do not impose a fixed memory cap on this portable runner.

## Measurement and export

The general path records thread CPU time and actual message sizes once. Its v2 causal replay colocates the coordinator with party 0 on the same virtual CPU/NIC, and enforces FIFO CPU and transmit scheduling with fair receiver bandwidth. LAN is 10 Gbit/s, RTT 2 ms; WAN is 0.2 Gbit/s, RTT 50 ms. This is **single-host computation with causal network replay**, not a physical cluster measurement. Preparation and compilation are outside online time; actual command and campaign durations are recorded separately.

`results.csv` includes actual input/XOR/AND counts, LAN/WAN seconds (or `single-core`), decimal total communication GB, proof MiB, verification ms, host cgroup peak bytes and available maximum prover RSS. Pappas RSS is the maximum native process-lifetime peak including preparation. Ours has no comparable per-party RSS measurement; that field is empty. Never divide the shared-host peak by N to invent per-party memory. Proof/verification scope is explicit in each case record.

The exported traces contain CPU intervals, dependencies and byte counts only. Replay a downloaded public trace independently:

```bash
PYTHONPATH=scripts python3 -m general.fast_replay --trace /path/to/public/traces/CASE
```

The compiled replay is checked against its Python reference in unit tests. Public bundles contain no private inputs, shares, `witness.bin`, `.private` files, raw prover logs, proof files or hashes of private inputs/proofs. Keep the whole `private/` directory local and share only `results-public.tar.gz`.

No original numerical matrix is asserted by this source release: the six-size monitored campaign and its final audit are separate. A fresh run's source manifest, toolchain/dependency identities, configuration, status and checks are exported with its measurements.
