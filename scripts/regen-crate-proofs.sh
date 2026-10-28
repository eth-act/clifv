#!/usr/bin/env bash
# Regenerate the generated crate proofs of crate-proofs/Crates/ (docs/USAGE.md, "Proving a crate").
# The generated files embed the compiler's output (CLIF, register allocations, executable bytes),
# so a PR that changes generated code reruns this script and commits the result.
#
# usage: scripts/regen-crate-proofs.sh
# Needs the tools of this checkout: `lake build lean-backend clif-decode link-check` and
# `cargo build --release -p cargo-fv -p clif-data-export -p lean-regalloc` (in rust/).
# Wrap it in scripts/memcap.sh when memory is shared.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
export PATH=$ROOT/rust/target/release:$PATH
OUT=../../crate-proofs/Crates

cd "$ROOT/examples/survey"
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
cargo fv build --keep-temps
exe=$(ls -t target/fv/plain/aarch64-unknown-linux-musl/debug/build/fv-demo/*/out/fv_demo 2>/dev/null | head -n 1 || true)
[ -n "$exe" ] || { echo "regen-crate-proofs: no fv_demo executable" >&2; exit 1; }
cargo fv link-proof --exe "$exe" --prune --lean "$OUT/FvDemo.lean" --module FvDemo
