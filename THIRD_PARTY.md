# Source provenance and third-party components

The artifact fetches fixed upstream dependencies at build time. They are ignored by Git and are not relicensed as our code.

| Component | Fixed version | Role / license information |
|---|---|---|
| [Binius64](https://github.com/binius-zk/binius64) | `4428e759dd27956bd5b9ae5025d67eb8ccc1accf` | Native ZK baseline and field/prover dependencies; upstream MIT/Apache-2.0 notices retained |
| [Code-Based Scalable coSNARKs](https://github.com/ChristodoulosPappas/Code-Based-Scalable-coSNARKs) | `1c50a7410fa464ad325e0014d0d5fedd196d86c5` | Pappas baseline. The fixed upstream tree has no repository-wide LICENSE file; its terms are not replaced by this artifact. Fetch directly from the author repository and consult its authors about redistribution rights. |
| XKCP | Archive supplied in the fixed Pappas tree | Precompiled `lib/libXKCP.a` and headers, hash verified. This artifact does not provide a rebuild of that upstream archive. |
| BLAKE3 and Rust crates | Cargo.lock / fixed Pappas tree | Respective upstream licenses; retained with downloaded source |
| Rust, CMake, Open MPI | `configs/toolchains.json` and detected compatible tools | Tooling installed or reused under the publishers' own licenses; actual versions recorded |

The collaborative protocol implementation and adapters come from the active paper implementation. The Keccak oracle and application relation/exporters provide independent statement checks. The generic source-path adjustment in the packaged exporter resolves the oracle inside this standalone repository; it changes no circuit or proof operation.

`SOURCE_MANIFEST.json` identifies included implementation/control sources. `third_party/*-files.json` identify required fixed upstream files. No private input, share, proof, proof hash, server credential, host configuration or parent Git history is included. The scope of any future release license must respect these third-party components.

## General-circuit update

`third_party/pappas-general.patch` contains the general frontend/index-binding integration, compact layout changes, Merkle fix and timing hooks relative to the same pinned author commit. Bootstrap fetches that commit directly, applies the patch in a fresh build tree and checks the resulting files against `pappas-general-files.json`. The upstream repository is not vendored in this release; its existing terms and notices remain applicable. `scripts/general/` supplies the signed Boolean relation exporter, thread-CPU MPI shim and v2 replay used with this adapter.

The packaged `binius-general` adapter adds preserved-graph Boolean inputs and a one-sample mode for the same task. Upstream Binius64 remains pinned and unmodified. The four historical configurations retain their explicit gamma871 identity; the new general entry uses gamma520/tau4/b3.
