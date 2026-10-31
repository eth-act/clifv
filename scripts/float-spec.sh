#!/usr/bin/env bash
# Build the FloatLib equality proofs (float-spec/, Lake package `fvFloatSpec`, library
# `FVFloatSpec`; docs/contracts/float.md, "Trust"), check that both toolchains elaborate the same
# FV/Float definitions, and audit the proofs' axioms.
# Usage: scripts/float-spec.sh [--no-audit]      (from anywhere in the worktree)
#
# float-spec/ is a separate Lake package with its own toolchain (float-spec/lean-toolchain,
# v4.35.0: FloatLib's and Mathlib's pin) and its own float-spec/.lake; it compiles the FV/Float
# cone (5 core-only modules) from the root sources itself. It never uses the shared Lake cache
# (the LAKE_* cache variables are unset here) and never writes into the root .lake. The first
# run clones FloatLib, Mathlib and their dependencies into float-spec/.lake/packages and fetches
# Mathlib's prebuilt oleans (`lake exe cache get`, ~1 GB download, ~7.5 GB unpacked) so that only
# FloatLib's ~200 modules, the FV/Float cone and FVFloatSpec build locally.
# Memory: every lake command runs under scripts/memcap.sh (FV_MEMCAP, default 16G here).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
export FV_MEMCAP="${FV_MEMCAP:-16G}" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
mc="$root/scripts/memcap.sh"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/float-spec_XXXXXX")"; trap 'rm -rf "$tmp"' EXIT

# 1. FV/Float as the compiler sees it: root toolchain, root .lake (shared cache allowed).
cd "$root"
"$mc" lake build FV.Float > /dev/null 2>&1 || { echo "float-spec: root FV.Float build failed" >&2; exit 1; }
"$mc" lake env lean float-spec/defs-hash.lean > "$tmp/root.txt"

# 2. float-spec on its own toolchain and .lake.
cd "$root/float-spec"
unset LAKE_ARTIFACT_CACHE LAKE_RESTORE_ARTIFACTS LAKE_CACHE_DIR FV_LAKE_CACHE
"$mc" lake exe cache get 2>&1 | tail -n 2   # Mathlib's olean cache: a no-op once unpacked.
"$mc" lake build 2>&1 | grep -vE '^(✔|⣿|trace)' | grep -E 'error|Build completed|failed' || true
"$mc" lake build > /dev/null 2>&1 || { echo "float-spec: build failed" >&2; exit 1; }
"$mc" lake env lean defs-hash.lean > "$tmp/spec.txt"

# 3. Same FV/Float definitions under both toolchains (docs/contracts/float.md, "Trust").
n=$(wc -l < "$tmp/root.txt")
if ! cmp -s "$tmp/root.txt" "$tmp/spec.txt" || [ "$n" -lt 100 ]; then
  diff "$tmp/root.txt" "$tmp/spec.txt" | cut -c1-200 | head -n 20 >&2 || true
  echo "float-spec: FV/Float definitions differ between $(cat "$root/lean-toolchain") and $(cat lean-toolchain) (FAIL)" >&2
  exit 1
fi
echo "ok FV/Float definitions identical under $(cat "$root/lean-toolchain") and $(cat lean-toolchain): $n constants, sha256 $(sha256sum < "$tmp/root.txt" | cut -c1-16)"

if [[ "${1:-}" != --no-audit ]]; then
  cd "$root"
  python3 scripts/axiom-audit.py --cwd float-spec float-spec/audit.lean
fi
