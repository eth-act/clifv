#!/usr/bin/env bash
# Differential test of the Lean IEEE core (FV/Float) against the host's IEEE 754 operations.
# Usage: scripts/float-difftest.sh [--aarch64] [--count N] [--seed S] [--only SUBSTR] [--rne-only]
#
# `float-difftest` (FVTest/Float/DiffTest.lean) prints edge-biased cases with the Lean results
# (default 100000 per class); `float-oracle` (rust/crates/float-oracle) recomputes them with
# Rust f32/f64 and compares bit-for-bit, NaN results as "both NaN". With --aarch64 the oracle
# is cross-compiled for aarch64-unknown-linux-musl and run under qemu-aarch64-static, and NaN
# results are compared bit-for-bit too (Arm FPCR = 0 NaN rules). See docs/contracts/float.md.
set -euo pipefail
cd "$(dirname "$0")/.."
aarch64=0
args=()
for a in "$@"; do
  if [[ $a == --aarch64 ]]; then aarch64=1; else args+=("$a"); fi
done
lake build float-difftest 2>&1 | tail -1
if [[ $aarch64 == 1 ]]; then
  : "${FLOAT_DIFFTEST_QEMU:=qemu-aarch64-static}"
  command -v "$FLOAT_DIFFTEST_QEMU" >/dev/null || { echo "missing $FLOAT_DIFFTEST_QEMU" >&2; exit 2; }
  if [[ -z "${FLOAT_DIFFTEST_LLD:-}" ]]; then
    sysroot="$(rustc --print sysroot)"
    FLOAT_DIFFTEST_LLD="$sysroot/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin/rust-lld"
  fi
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER="$FLOAT_DIFFTEST_LLD" \
    cargo build --quiet --release --manifest-path rust/Cargo.toml -p float-oracle \
    --target aarch64-unknown-linux-musl
  oracle=("$FLOAT_DIFFTEST_QEMU" rust/target/aarch64-unknown-linux-musl/release/float-oracle --exact-nan)
else
  cargo build --quiet --release --manifest-path rust/Cargo.toml -p float-oracle
  oracle=(rust/target/release/float-oracle)
fi
.lake/build/bin/float-difftest "${args[@]}" | "${oracle[@]}"
