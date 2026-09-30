#!/usr/bin/env bash
# Negative control for scripts/rust-clif/diff-native.sh: mutate single instructions of
# corpus functions, compile the MUTATED file with the Lean backend and diff it against
# Cranelift's code for the ORIGINAL file. Each mutation must be reported as a disagreement
# (return value, memory through an sret pointer, memory through pointer arguments / the panic
# path), and an unmutated function of the same files must still agree.
# Needs a diff-native.sh run (its normalised files and runtime object).
# usage: scripts/rust-clif/diff-native-selftest.sh [DIFF_WORK]
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
work=${1:-${DIFF_WORK:-/tmp/rust-clif-survey/diff-native}}
native="$root/rust/target/release/clif-native"
backend="$root/.lake/build/bin/lean-backend"
t=$(mktemp -d /tmp/diff-native-selftest.XXXXXX)
trap 'rm -rf "$t"' EXIT
ulimit -c 0

# FILE FUNCTION OLD NEW: replace OLD by NEW (once) inside FUNCTION's body
mutate() {
  python3 - "$@" <<'EOF'
import sys
path, fn, old, new = sys.argv[1:5]
src = open(path).read()
start = src.index(f"function %{fn}(")
end = src.index("\n}", start)
body = src[start:end]
assert old in body, (fn, old)
open(path, "w").write(src[:start] + body.replace(old, new, 1) + src[end:])
EOF
}

fail=0
check() { # CRATE MUTATED_FN CONTROL_FN
  local pc=$1 fn=$2 control=$3
  "$backend" "$t/$pc.clif" "$t/$pc.o" --traps "$t/$pc.traps.json" >/dev/null 2>&1
  "$native" --diff "$work/$pc.clif" --lean-obj "$t/$pc.o" --lean-table "$t/$pc.traps.json" \
    --link "$work/rust-runtime.o" --vectors 32 --min-vectors 0 --only "$fn" --only "$control" \
    >"$t/$pc.$fn.jsonl" || true
  python3 - "$t/$pc.$fn.jsonl" "$fn" "$control" <<'EOF' || fail=1
import json, sys
recs = {r["func"]: r for r in map(json.loads, open(sys.argv[1])) if "func" in r}
fn, control = recs[sys.argv[2]], recs[sys.argv[3]]
ok = fn["disagree"] > 0 and control["disagree"] == 0 and control["agree"] > 0
print(f"{'ok  ' if ok else 'FAIL'} mutated %{fn['func']}: {fn['disagree']} of {fn['vectors']} vectors disagree "
      f"(e.g. {json.dumps(fn['examples'][:1])[:300]}); control %{control['func']}: agree {control['agree']}")
sys.exit(0 if ok else 1)
EOF
}

cp "$work/release-a_arith.clif" "$t/release-a_arith.clif"
mutate "$t/release-a_arith.clif" add_u32 "iadd.i32 v2, v3" "isub.i32 v2, v3"
check release-a_arith add_u32 mul_i32

cp "$work/release-b_slices.clif" "$t/release-b_slices.clif"
mutate "$t/release-b_slices.clif" make_array "iconst.i64 63" "iconst.i64 62"
check release-b_slices make_array array_index

cp "$work/release-b_slices.clif" "$t/release-b_slices.clif"
mutate "$t/release-b_slices.clif" swap_ends "v9 = iconst.i64 1" "v9 = iconst.i64 2"
check release-b_slices swap_ends copy_into

exit $fail
