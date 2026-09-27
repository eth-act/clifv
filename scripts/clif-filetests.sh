#!/usr/bin/env bash
# Run Cranelift's runtests through Clif.run (Lean) and through the Cranelift interpreter
# (clif-oracle), compare both with the `; run:` expectations and with each other, and
# check that the Lean printer's output is accepted by cranelift-reader + the verifier.
#
# usage: scripts/clif-filetests.sh [-v] [FILE.clif...]
#   default files: third_party/wasmtime/cranelift/filetests/filetests/runtests/*.clif
#
# Exit status 0 iff no run failed, no Lean/interpreter disagreement, no round-trip failure,
# and every printed file passes `clif-oracle check`.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

VERBOSE=()
if [[ "${1:-}" == "-v" ]]; then VERBOSE=(-v); shift; fi
if [[ $# -gt 0 ]]; then
  FILES=("$@")
else
  FILES=(third_party/wasmtime/cranelift/filetests/filetests/runtests/*.clif)
fi

cargo build --quiet --release --manifest-path rust/Cargo.toml -p clif-oracle
lake build clif-filetest >/dev/null
ORACLE=rust/target/release/clif-oracle
FILETEST=.lake/build/bin/clif-filetest

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/oracle" "$WORK/printed" "$WORK/printed-oracle"

for f in "${FILES[@]}"; do
  "$ORACLE" interp "$f" > "$WORK/oracle/$(basename "$f").json" || true
done

status=0
echo "== Clif.run vs expectations and vs the Cranelift interpreter"
"$FILETEST" "${VERBOSE[@]}" --oracle-dir "$WORK/oracle" --print-dir "$WORK/printed" \
  "${FILES[@]}" | tee "$WORK/lean.txt" || status=1

echo "== Printed programs: cranelift-reader + verifier"
checked=0; rejected=0
for p in "$WORK/printed"/*.clif; do
  [[ -e "$p" ]] || continue
  checked=$((checked + 1))
  if ! "$ORACLE" check "$p" > "$WORK/check.txt" 2>&1; then
    rejected=$((rejected + 1)); status=1
    cat "$WORK/check.txt"
  fi
  "$ORACLE" interp "$p" > "$WORK/printed-oracle/$(basename "$p").json" || true
done
echo "printed files: $checked, rejected by cranelift: $rejected"

echo "== Printed programs re-run (Clif.run vs interpreter on the printed text)"
printed=("$WORK/printed"/*.clif)
if [[ -e "${printed[0]}" ]]; then
  "$FILETEST" --oracle-dir "$WORK/printed-oracle" "${printed[@]}" | tail -1 || status=1
fi

echo "== Summary"
tail -1 "$WORK/lean.txt"
echo "printed: $checked files, rejected $rejected"
exit $status
