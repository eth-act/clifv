#!/usr/bin/env bash
# Check `Clif.runX` (CLIF with unwinding, FV/Clif/Unwind.lean) against native runs: every
# `; run:` line of the fixtures runs natively on the host through Cranelift's JIT, its
# exception tables and `__cranelift_throw` (`clif-throw-native`), and through `Clif.runX`
# (`clif-filetest --unwind`); both are compared with the expectations and with each other.
# The Cranelift interpreter has no exceptions (`TryCall => unimplemented!`), so this is the
# oracle of the exceptional edge (S10b, docs/plans/unwinding.md).
#
# usage: scripts/clif-unwind-native.sh [FILE.clif...]
#   default files: FVTest/Clif/fixtures/unwind/*.clif
#
# Exit status 0 iff every run passes on both sides and they agree.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

if [[ $# -gt 0 ]]; then FILES=("$@"); else FILES=(FVTest/Clif/fixtures/unwind/*.clif); fi

cargo build --quiet --release --manifest-path rust/Cargo.toml -p clif-throw-native
lake build clif-filetest >/dev/null
NATIVE=rust/target/release/clif-throw-native
FILETEST=.lake/build/bin/clif-filetest

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

status=0
echo "== Native runs (clif-throw-native) vs expectations"
for f in "${FILES[@]}"; do
  out="$WORK/$(basename "$f").json"
  "$NATIVE" "$f" > "$out" || status=1
  python3 - "$f" "$out" <<'EOF' || status=1
import json, sys
f, path = sys.argv[1], sys.argv[2]
ok = bad = 0
for line in open(path):
    r = json.loads(line)
    if "file_error" in r:
        print(f"{f}: native file error: {r['file_error']}"); sys.exit(1)
    a, e = r["actual"], r["expected"]
    good = e is None or ("returned" in a and (a["returned"] == e["values"]) == (e["cmp"] == "=="))
    if good: ok += 1
    else:
        bad += 1; print(f"  NATIVE FAIL %{r['func']}: {a}")
print(f"{f}: native pass {ok} fail {bad}")
sys.exit(1 if bad else 0)
EOF
done

echo "== Clif.runX vs expectations and vs the native runs"
"$FILETEST" -v --unwind --oracle-dir "$WORK" "${FILES[@]}" || status=1
exit $status
