#!/usr/bin/env bash
# Build the FloatLib equality proofs (float-spec/, Lake package `fvFloatSpec`, library
# `FVFloatSpec`; docs/contracts/float.md, "Trust") and audit their axioms.
# Usage: scripts/float-spec.sh [--no-audit]      (from anywhere; uses the worktree's FV build)
#
# float-spec/ is the only part of clifv that depends on FloatLib and Mathlib; the root package
# (`lake build FV`) does not clone or load them. The first run clones FloatLib, Mathlib and their
# dependencies into float-spec/.lake/packages and fetches Mathlib's prebuilt oleans
# (`lake exe cache get`, ~1 GB download, ~7.5 GB unpacked) so that only FloatLib's ~200 modules
# and FVFloatSpec build locally (cold: ~6 min wall, peak ~2.6 GB per lean process).
# Memory: every lake command runs under scripts/memcap.sh (FV_MEMCAP, default 16G here).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root/float-spec"
export FV_MEMCAP="${FV_MEMCAP:-16G}" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
mc="$root/scripts/memcap.sh"
# Mathlib's olean cache: a no-op once the oleans are unpacked.
"$mc" lake exe cache get 2>&1 | tail -n 2
"$mc" lake build 2>&1 | grep -vE '^(✔|⣿|trace)' | grep -E 'error|Build completed|failed' || true
"$mc" lake build > /dev/null 2>&1 || { echo "float-spec: build failed" >&2; exit 1; }
if [[ "${1:-}" != --no-audit ]]; then
  cd "$root"
  python3 scripts/axiom-audit.py --cwd float-spec float-spec/audit.lean
fi
