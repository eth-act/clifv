#!/usr/bin/env bash
# Write <crate>/tests/expected.txt for the nine survey crates: the cases of <crate>/cases.rs
# computed by rustc's LLVM backend for aarch64-unknown-linux-musl (run under qemu), i.e. the
# reference `cargo fv test` is checked against. Debug profile, like the tests.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER=rust-lld
export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER=qemu-aarch64-static
cargo +"${TOOLCHAIN:-nightly-2026-09-26}" build -q --manifest-path "$here/expect/Cargo.toml" \
  --target aarch64-unknown-linux-musl
bin="$here/expect/target/aarch64-unknown-linux-musl/debug/survey-expect"
for c in a_arith b_slices c_structs_enums d_loops_iters e_option_result f_crypto g_u128 h_dyn_generic i_alloc; do
  qemu-aarch64-static "$bin" "$c" >"$here/$c/tests/expected.txt"
  echo "$c: $(wc -l <"$here/$c/tests/expected.txt") values"
done
