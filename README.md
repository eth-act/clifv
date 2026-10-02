# clifv

## Using it from cargo: `cargo fv`

`cargo fv build|run|test` builds a Rust crate the way `cargo build|run|test` does. The
frontend is rustc_codegen_cranelift, and every function of your crate **and of its
dependencies** (every crate compiled for the target; `--members-only` restricts it to the
workspace) that the Lean backend supports is compiled by the Lean backend; the other functions
keep cg_clif's code. Not compiled by us: std (prebuilt), and build scripts and proc macros
(host code, not part of the program). The target
is `aarch64-unknown-linux-musl`, and executables run under `qemu-aarch64-static`. After each
build, `target/fv-report.json` (also printed by `cargo fv report`) lists, per crate and per
function, whether the function is verified (inside `E2E.backend_correct_final`), compiled but
unverified (with the reason), or left to Cranelift (with the reason).

```
cd rust && cargo build --release -p cargo-fv -p clif-data-export -p lean-regalloc
export PATH=$PWD/target/release:$PATH
cd ../examples/fv-demo && cargo fv test
```

See [docs/USAGE.md](docs/USAGE.md) for installation, options, how it works, what is verified,
and limitations. The examples are `examples/fv-demo`, `examples/survey`, `examples/vendor`
and `examples/deps` (real crates.io dependencies: serde/serde_json, regex, sha2, num-bigint,
rand, …), and
`examples/compare.sh` compares a crate's `cargo test` results (LLVM) with `cargo fv test`.
