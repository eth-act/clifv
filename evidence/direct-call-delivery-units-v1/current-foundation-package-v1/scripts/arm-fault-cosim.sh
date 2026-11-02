#!/usr/bin/env bash
# Co-simulation of memory faults: ArmFault.stepF against qemu-aarch64-static (A3, #412).
# Usage: scripts/arm-fault-cosim.sh [--n N] [--seed S] [--only SUBSTR] [--show K]
# See FVTest/Arm/Cosim/Fault.lean and docs/contracts/arm.md ("Memory faults").
set -euo pipefail
cd "$(dirname "$0")/.."
: "${ARM_COSIM_CLANG:=clang}"
if [[ -z "${ARM_COSIM_LLD:-}" ]]; then
  sysroot="$(rustc --print sysroot 2>/dev/null || true)"
  cand="$sysroot/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin/rust-lld"
  if [[ -x "$cand" ]]; then ARM_COSIM_LLD="$cand"; else ARM_COSIM_LLD="rust-lld"; fi
fi
: "${ARM_COSIM_QEMU:=qemu-aarch64-static}"
export ARM_COSIM_CLANG ARM_COSIM_LLD ARM_COSIM_QEMU
lake build arm-fault-cosim
exec .lake/build/bin/arm-fault-cosim "$@"
