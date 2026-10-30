# Measurement and implementation notes

## Reproduction boundary

This repository packages the active collaborative PCS/PIOP implementations, the native Binius64 adapter, the Pappas PCS/Keccak adapters, independent statement checks, and the common timing replay. It does not contain original private inputs, proof files, old experiment logs or the parent project's Git history. Running it generates a new run, not a copy of the original measurements.

The scientific defaults are in `configs/experiments.json`. Build/setup and optional memory/watchdog overrides are operational settings and are recorded separately. Neither resource discovery nor dependency installation changes N, task size, gamma, tau or network parameters. A failed configuration stops the run; success requires both its validation checks and resource admission.

## Offline preparation and memory

Our application adapter prepares fresh shares and correlated mask material in the stated ideal preprocessing model. Preparation serializes party files; on Linux it synchronizes completed writes and requests `POSIX_FADV_DONTNEED`, and requests cache release after reading. These calls occur before online timing. They avoid retaining redundant file-cache copies of private state; no timed computation, randomness, message or proof format is changed.

Pappas Keccak uses the same RAM-streamed preparation adapter as the measured implementation. It limits the dealer's extra temporary copy without changing shares or subsequent random state. Its batch buffer is an operational allocation cap, bounded by available memory. Pappas PCS uses the original RAM-backed temporary preparation path. The runner does not replace timed kernels with disk operations or estimates.

The per-case memory budget is 90% of the minimum of host `MemAvailable` and every visible ancestor's `memory.max - memory.current`. Unlimited ancestors do not impose a zero limit. A smaller explicit override is allowed. Cases run in a fresh systemd cgroup. Before any proof starts, the service recomputes its actual ancestor capacity, excluding its own provisional leaf limit, and applies the smaller of the launcher and service budgets. It verifies `MemoryMax` and `MemorySwapMax=0` and records ancestor-event increments as well as leaf events. Limits are rounded down to whole memory pages. Public records include peak usage, OOM/limit events, memory pressure and selected memory statistics. A case is not resource-admitted if it reaches its limit, swaps, is killed or fails to finish. Detected capacity can change between cases; each actual budget is recorded.

The operating system may still reclaim clean pages below a limit. Zero cgroup limit events are not a claim that the OS performs no memory management. The artifact never estimates or subtracts those costs.

## Online computation and communication

Our simulation runs the actual coordinator and worker kernels, using a separate persistent process per application worker. It records each command's coordinator interval, each worker interval, request/response byte lengths and final serialization. The replay preserves round dependencies; it adds the coordinator and slowest required worker on the corresponding critical path. Rank 0 and the coordinator are colocated in the virtual model.

The Pappas path uses MPI with a PMPI tracing library. A token serializes measured computation on the selected CPU while other CPUs handle progress. Send/receive, nonblocking request/wait and collective dependencies are recorded. The exported trace contains timing/size metadata, not message payloads.

The common causal replay uses a FIFO sender interface, fair sharing of a receiver's bandwidth, and half an RTT per directed message. Results contain online time, the zero-network compute critical path, their difference and transmitted bytes. It models a network; it is not a measurement of N physical servers. `execution_wall_s` includes actual sequential execution, preparation and checking and therefore can be far larger.

The native Binius64 adapter caches only circuit-dependent public setup offline, restores its prover cache and constructs the witness before its timed native zero-knowledge proof call. Native proof generation is directly timed on one core. It includes its native zero-knowledge wrapper and does not use the collaborative network replay.

## Statements and verification

Application workloads use full 24-round Keccak-f[1600]. Each private input is 1600 bits and each public output is its first 256 bits, with byte-order/LSB conventions fixed by the shared oracle/exporter. Prefixes of one freshly generated master input are reused across schemes in a run.

For standalone PCS, a deterministic shared bit table controls M. The Pappas adapter uses its native field and an externally specified point/claim; our adapter retains its own native field/point construction. Input length and contents are shared, while fields, padding and security configurations remain implementation-specific.

Our application and PCS, Pappas PCS and native Binius64 have public verification and negative corruption controls. The Pappas Keccak path checks completion of the author's phases and absence of reported native errors; it lacks an independent full verifier/complete serialized proof. Its validation flag remains false for full-proof verification, including smoke runs.

These executions exercise the paper's ideal secure aggregation, randomness and correlated sharing interfaces. They are not an implementation or security certification of a malicious-secure distributed preprocessing service. Offline costs are not included in reported online time.

## Source adaptations

The packaged core and proof adapters preserve the active algorithms. Pappas staging applies the existing external-input readers, RAM preparation, wide integer indexing, correction of the second Merkle child index, and timing-boundary hooks. The transformed measured files are checked against fixed hashes in `configs/toolchains.json`. Binius64 source is fixed by commit plus a 678-file manifest. Baselines are not retuned to match our security parameters.

Original formal results remain in the parent project and are not embedded here. Reproduction records actual compiler/MPI versions, source identities, CPU policy and memory budgets so different-machine results can be assessed without claiming identical binaries or timing.
