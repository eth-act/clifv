#!/usr/bin/env bash
# Run Charon then Aeneas on extract/rust/entry under the resource rule.
# Logs: $CLIFV_EXTRACT_WORK/runs/<UTC>/{charon,aeneas}.log with {charon,aeneas}.exit.
# Exits 0 once both tools ran (whatever their exit codes) so the report always runs;
# prints the run directory on the last line.
set -uo pipefail
EXTRACT=$(cd "$(dirname "$0")/.." && pwd)
ROOT=$(dirname "$EXTRACT")
WORK=${CLIFV_EXTRACT_WORK:-/data/clifv-extract}
RUN=$WORK/runs/$(date -u +%Y%m%dT%H%M%SZ)
mkdir -p "$RUN"
export OMP_NUM_THREADS=2 OMP_THREAD_LIMIT=2 LEAN_NUM_THREADS=2 CARGO_BUILD_JOBS=2
# One heavy command at a time across all agents/scripts (resource rule): $WORK/heavy.lock.
heavy() { flock "$WORK/heavy.lock" env FV_MEMCAP=64G bash "$ROOT/scripts/memcap.sh" nice -n 10 "$@"; }
patterns() { [ -f "$1" ] && grep -v '^\s*#' "$1" | grep -v '^\s*$' | cut -f1; }

args=(--preset=aeneas --sysroot default
  --start-from crate::compile_aarch64 --start-from crate::triple
  --include cranelift_codegen --include cranelift_reader --include cranelift_entity
  --include cranelift_bforest --include cranelift_bitset --include cranelift_control
  --include cranelift_codegen_shared --include wasmtime_internal_core
  --include regalloc2
  # Fork options: layouts are unused by Aeneas (and stale after associated-type lifting);
  # ISLE-generated bodies explode under duplicating control-flow reconstruction.
  --no-layouts --code-duplication-limit "${CLIFV_DUP_LIMIT:-2}"
  # Monomorphize the extracted crates (not std/foreign crates, whose items keep matching the
  # Aeneas library models): removes the recursive groups mixing ISLE functions with the
  # IsleContext impl, and the associated-type cycles of the MachInst/ABIMachineSpec traits.
  --monomorphize-local-only)
while IFS= read -r p; do args+=(--opaque "$p"); done < <(patterns "$EXTRACT/opaque.txt")
while IFS= read -r p; do args+=(--opaque "$p"); done < <(patterns "$EXTRACT/overrides.txt")
while IFS= read -r p; do args+=(--devirtualize "$p"); done < <(patterns "$EXTRACT/devirtualize.txt")
# Experiments only: extra Charon arguments (word-split).
# shellcheck disable=SC2206
[ -n "${CLIFV_CHARON_EXTRA:-}" ] && args+=($CLIFV_CHARON_EXTRA)
LLBC=$RUN/entry.llbc
if [ -n "${CLIFV_REUSE_RUN:-}" ]; then
  # Iterating on Aeneas only: reuse an earlier run's LLBC and Charon results.
  for f in entry.llbc charon.cmd charon.log charon.exit; do ln -s "$CLIFV_REUSE_RUN/$f" "$RUN/$f"; done
else
  printf '%q ' charon cargo "${args[@]}" --dest-file "$LLBC" > "$RUN/charon.cmd"
  (cd "$EXTRACT/rust/entry" && heavy "$WORK/tools/charon/bin/charon" cargo "${args[@]}" \
    --dest-file "$LLBC" -- --locked --lib --jobs 1) > "$RUN/charon.log" 2>&1
  echo $? > "$RUN/charon.exit"
fi

GEN=$EXTRACT/lean/Generated
rm -rf "$GEN"; mkdir -p "$GEN"
if [ -f "$LLBC" ]; then
  # -filter-trait-methods: trait impls only provide the methods of the library's model of
  # the trait (e.g. Iterator: next, size_hint, ...), not its ~75 default methods.
  (cd "$EXTRACT" && heavy "$WORK/tools/aeneas/bin/aeneas" -backend lean -split-files -emit-json \
    -sequential -no-progress-bar -print-error-emitters -print-error-diagnostics -all-computable \
    -filter-trait-methods -dest "$GEN" -subdir ClifvGen "$LLBC") > "$RUN/aeneas.log" 2>&1
  echo $? > "$RUN/aeneas.exit"
  # TypesExternal/FunsExternal: the templates minus the items with a handwritten model.
  python3 "$EXTRACT/scripts/externals.py" "$GEN" > "$RUN/externals.json"
else
  echo "no LLBC" > "$RUN/aeneas.log"; echo 255 > "$RUN/aeneas.exit"
fi
echo "$RUN"
