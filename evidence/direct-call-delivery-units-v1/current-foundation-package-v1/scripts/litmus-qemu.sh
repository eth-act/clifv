#!/usr/bin/env bash
# Litmus tests of the atomics code Cranelift emits, run under qemu-aarch64-static (T2c, #301).
# Every observed outcome must be allowed by the Armv8 model of FV/Concurrency/Armv8.lean: the
# forbidden outcomes are the ones proven inconsistent in FVTest/Concurrency/Litmus.lean (herd7's
# aarch64.cat verdicts). qemu is not weak-memory faithful: unobserved allowed outcomes are fine.
# Usage: scripts/litmus-qemu.sh [iterations]   (default 20000 per test)
set -euo pipefail
cd "$(dirname "$0")/.."
: "${LITMUS_QEMU:=qemu-aarch64-static}"
command -v "$LITMUS_QEMU" >/dev/null || { echo "missing $LITMUS_QEMU" >&2; exit 2; }
if [[ -z "${LITMUS_LLD:-}" ]]; then
  sysroot="$(rustc --print sysroot)"
  LITMUS_LLD="$sysroot/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin/rust-lld"
fi
out="${TMPDIR:-/tmp}/litmus-qemu-$$"
trap 'rm -f "$out"' EXIT
rustc --edition 2021 -O --target aarch64-unknown-linux-musl -C linker="$LITMUS_LLD" \
  tools/litmus/litmus.rs -o "$out"
"$LITMUS_QEMU" "$out" "$@"
