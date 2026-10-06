# clifv

clifv compiles Cranelift IR (CLIF) to AArch64 machine code. The compiler is written in Lean 4.
For register allocation it runs regalloc2, checks the result in Lean, and falls back to a
proven Lean allocator if the check fails.

The end-to-end theorem `E2E.backend_correct_final` states that the Arm code of a function in
its scope refines the function's CLIF semantics. Its premises include contracts for the
function's callees and for the ABI; [docs/contracts/e2e.md](docs/contracts/e2e.md) lists them
all. The proofs contain no `sorry` and declare no axioms. They trust Lean's kernel and
compiled evaluation (`bv_decide`, `native_decide`), the CLIF semantics, the Arm model, rustc
and cg_clif, and the code outside the Lean-compiled functions: std, musl, and functions left
to cg_clif. [docs/USAGE.md](docs/USAGE.md#what-is-verified-and-what-is-not) lists everything
else that is trusted.

The main use is compiling Rust: rustc_codegen_cranelift (cg_clif) lowers Rust to CLIF, and
clifv's Lean backend compiles that CLIF to machine code.

## `cargo fv`

`cargo fv build|run|test` works like `cargo build|run|test`, except that the Lean backend
compiles every function it supports, in your crate and in all its dependencies. A function the
Lean backend cannot compile keeps cg_clif's code, so the Lean backend never makes a build fail.
`--members-only` limits the Lean backend to the workspace members. We do not compile std,
which comes prebuilt, or build scripts and proc macros, which run on the host and are not part
of the program.

Executables target `aarch64-unknown-linux-musl` and run under `qemu-aarch64-static`.

After each build, `target/fv-report.json` lists every function of your crate and its
dependencies as verified (covered by an end-to-end theorem), compiled but unverified, or left
to cg_clif. The last two give a reason. `cargo fv report` prints the summary again.

## Quick start

Install Lean 4 through elan. Install the pinned Rust nightly with cg_clif,
`qemu-aarch64-static`, LLVM 18 binutils, and python3, as [docs/USAGE.md](docs/USAGE.md#install)
describes. Then, from the repository root, build the tools and run an example:

```
scripts/memcap.sh lake build lean-backend
scripts/memcap.sh scripts/build-cg-clif-unwind.sh
cd rust && ../scripts/memcap.sh cargo build --release -p cargo-fv -p clif-data-export -p lean-regalloc
export PATH=$PWD/target/release:$PATH
cd ../examples/fv-demo && cargo fv test
```

`scripts/memcap.sh` caps each build at 16 GB of memory (`FV_MEMCAP` changes the cap), so a
runaway Lean process cannot exhaust the machine. `scripts/build-cg-clif-unwind.sh` builds
cg_clif with landing pads. The shipped cg_clif has none, and without them fv-demo's four
unwinding tests fail.

After each build, `cargo fv` also checks every linked executable against the binary-level
theorem. The check needs the `link-check` tool, which takes close to an hour to build on a
16-core machine and more memory than the default cap:

```
FV_MEMCAP=24G scripts/memcap.sh lake build link-check
```

Without `link-check`, `cargo fv` reports each executable as not checked. `--no-binary-check`
skips the check.

## Examples

| Example | Contents |
| --- | --- |
| [examples/fv-demo](examples/fv-demo) | arithmetic, slices, enums, iterators, `u128`, `dyn` traits, and unwinding through Lean-compiled frames |
| [examples/survey](examples/survey) | nine small crates, one per area: arithmetic, slices, structs and enums, loops and iterators, `Option`/`Result`, crypto, `u128`, `dyn` and generics, allocation |
| [examples/vendor](examples/vendor) | vendored crates.io crates: bitflags, cfg-if, crc32fast, hex, itoa, memchr, once_cell |
| [examples/deps](examples/deps) | a crate with real crates.io dependencies: serde_json, regex, sha2, num-bigint, rand, … |

`examples/compare.sh DIR` runs a crate's tests under `cargo test` (LLVM) and under
`cargo fv test`, and compares the outcomes.

## Documentation

- [docs/USAGE.md](docs/USAGE.md): installation, options, what is verified, and limitations
- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): the components, the end-to-end theorems, and their trust base
- [docs/PLAN.md](docs/PLAN.md): the design plan and the status of each milestone
- [docs/TO-PROVE.md](docs/TO-PROVE.md): what remains to be proven
- [AGENTS.md](AGENTS.md): coordination rules for contributors and their agents
