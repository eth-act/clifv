#!/usr/bin/env bash
# Regenerate the generated crate proofs of crate-proofs/Crates/ (docs/USAGE.md, "Proving a crate").
# The generated files embed the compiler's output (CLIF, register allocations, executable bytes),
# so a PR that changes generated code reruns this script and commits the result. The CI full gate
# reruns it and fails on any difference from the committed files (#994).
#
# usage: scripts/regen-crate-proofs.sh
# Needs the tools of this checkout: `lake build lean-backend clif-decode link-check dead-cleanup-generate` and
# `cargo build --release -p cargo-fv -p clif-data-export -p lean-regalloc` (in rust/), and the
# patched cg_clif (scripts/build-cg-clif.sh). Wrap it in scripts/memcap.sh when memory is shared.
#
# The output does not depend on where the checkout or the Rust toolchain is (#984), so two
# machines regenerate the same files:
#   - rustc gets `--remap-path-prefix` for the repository (`/clifv`) and for the toolchain's
#     library sources (`/rustc/<commit>`, the name rustc itself uses without the `rust-src`
#     component). Otherwise the executables hold both paths: the checkout's in their debug
#     sections (which moves the symbol table and the section headers the proofs quote), `$HOME`'s
#     in the panic locations of inlined std code (data objects the proofs quote).
#   - With a `--remap-path-prefix` among RUSTFLAGS cargo leaves RUSTFLAGS out of the hash in its
#     file names (`-<16 hex>`), which cargo fv's symbol prefixes (`__fv_<12 hex>_`) are derived
#     from; without it the absolute path of cg_clif (`-Zcodegen-backend=…`) is in that hash.
#   - The builds use target directories of their own (target/regen, target/pipeline-t), removed
#     first: a build left by `cargo fv test` cannot change the result.
#   - The generated files name the executable by its path inside the repository.
# The generated modules are removed first, so a step that writes nothing (a missing tool, a
# failed link-proof) leaves a visible difference instead of the old files.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
export PATH=$ROOT/rust/target/release:$PATH
OUT=../../crate-proofs/Crates
TC=${FV_TOOLCHAIN:-nightly-2026-09-26}
sysroot=$(rustc +"$TC" --print sysroot)
commit=$(rustc +"$TC" -vV | sed -n 's/^commit-hash: //p')
[ -n "$commit" ] || { echo "regen-crate-proofs: no commit-hash in rustc +$TC -vV" >&2; exit 1; }
# cargo fv appends its own flags to these (it reads CARGO_ENCODED_RUSTFLAGS before RUSTFLAGS)
export CARGO_ENCODED_RUSTFLAGS="--remap-path-prefix=$sysroot/lib/rustlib/src/rust=/rustc/$commit"$'\x1f'"--remap-path-prefix=$ROOT=/clifv"
for ex in survey fv-demo; do
  rm -rf "$ROOT/examples/$ex/target/regen" "$ROOT/examples/$ex/target/pipeline-t"
done
# the modules this script writes: Crates/<M>.lean and, when link-check splits it, Crates/<M>/
GEN=(AArith BSlices CStructsEnums DLoopsIters EOptionResult FCrypto GU128 HDynGeneric IAlloc AArithAbort FvDemo
  InScopeInputs/AArith InScopeInputs/FvDemo DeadCleanupGenerated DeadCleanupGeneratedSplit)
for m in "${GEN[@]}"; do
  rm -rf "$ROOT/crate-proofs/Crates/$m.lean" "$ROOT/crate-proofs/Crates/$m"
done

cd "$ROOT/examples/survey"
export CARGO_TARGET_DIR=$PWD/target/regen
cargo fv test --keep-temps || true   # the test results do not matter, the kept inputs do
for spec in a_arith:AArith b_slices:BSlices c_structs_enums:CStructsEnums d_loops_iters:DLoopsIters \
    e_option_result:EOptionResult f_crypto:FCrypto g_u128:GU128 h_dyn_generic:HDynGeneric i_alloc:IAlloc; do
  c=${spec%%:*}; m=${spec##*:}
  cargo fv link-proof --exe "/$c/" --exe /values- --crate "$c" --prune --lean "$OUT/$m.lean" --module "$m"
done

# a_arith with panic=abort (the configuration of Crates.BinaryWitness)
cargo fv test --panic-abort --keep-temps || true
cargo fv link-proof --mode plain-abort --exe /a_arith/ --exe /values- --crate a_arith --prune \
  --lean "$OUT/AArithAbort.lean" --module AArithAbort

# fv-demo: its binary (the build also links the test executables)
cd "$ROOT/examples/fv-demo"
export CARGO_TARGET_DIR=$PWD/target/regen
cargo fv build --keep-temps
exe=$(ls -t target/regen/fv/plain/aarch64-unknown-linux-musl/debug/build/fv-demo/*/out/fv_demo 2>/dev/null | head -n 1 || true)
[ -n "$exe" ] || { echo "regen-crate-proofs: no fv_demo executable" >&2; exit 1; }
cargo fv link-proof --exe "$exe" --prune --lean "$OUT/FvDemo.lean" --module FvDemo

# Crates/InScopeInputs (Crates.InScopeWitness): a_arith and fv-demo compiled by `pipeT`'s pipeline
# (`lean-backend --pipeline-t`, the compiler `crate_correct_inScope` covers), own target
# directories; `link-check --input-only` writes the input alone.
export FV_PIPELINE_T=1
cd "$ROOT/examples/survey"
export CARGO_TARGET_DIR=$PWD/target/pipeline-t
cargo fv test -p a_arith --keep-temps || true
cargo fv link-proof --exe /a_arith/ --exe /values- --crate a_arith || true
"$ROOT/.lake/build/bin/link-check" target/pipeline-t/fv/link-proof \
  --input-only "$OUT/InScopeInputs/AArith.lean" --module InScopeInputs.AArith
cd "$ROOT/examples/fv-demo"
export CARGO_TARGET_DIR=$PWD/target/pipeline-t
cargo fv build --keep-temps
exe=$(ls -t target/pipeline-t/fv/plain/aarch64-unknown-linux-musl/debug/build/fv-demo/*/out/fv_demo 2>/dev/null | head -n 1 || true)
[ -n "$exe" ] || { echo "regen-crate-proofs: no pipeline-t fv_demo executable" >&2; exit 1; }
cargo fv link-proof --exe "$exe" || true
"$ROOT/.lake/build/bin/link-check" target/pipeline-t/fv/link-proof \
  --input-only "$OUT/InScopeInputs/FvDemo.lean" --module InScopeInputs.FvDemo

# The closed cleanup fixtures of #137 (Crates/DeadCleanupGenerated, Crates/DeadCleanupGeneratedSplit,
# #745): compiled and written by `dead-cleanup-generate` (FVTest/Link/DeadCleanupGenerate.lean).
cd "$ROOT"
"$ROOT/.lake/build/bin/dead-cleanup-generate" crate-proofs/Crates

# link-check names the executable by its absolute path (in comments only): make it the path
# inside the repository (a literal replacement: the checkout's path is not a pattern)
written=()
for m in "${GEN[@]}"; do
  [ -f "crate-proofs/Crates/$m.lean" ] || { echo "regen-crate-proofs: crate-proofs/Crates/$m.lean was not written" >&2; exit 1; }
  written+=("crate-proofs/Crates/$m.lean")
  for f in "crate-proofs/Crates/$m"/*.lean; do
    # a module that is not split has no directory
    if [ -f "$f" ]; then written+=("$f"); fi
  done
done
python3 scripts/strip-path-prefix.py "$ROOT/" "${written[@]}"
