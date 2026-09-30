#!/usr/bin/env bash
# Native differential test of the Lean backend over the whole Rust survey corpus: every
# function of every dumped crate (debug / release / release-oc), Lean-backend object vs
# Cranelift's own aarch64 code for the same CLIF, called with generated inputs under
# qemu-aarch64-static (`clif-native --diff`, docs/research/rust-route.md "Native coverage").
#
# Per crate: normalise the unopt dump with its recovered data image and callee names
# (clif-data-export --fnmap), compile it with `lean-backend`, then `clif-native --diff` links
# both engines' objects with the same harness, trampolines, data objects (fixed addresses)
# and runtime (scripts/rust-clif/rust-runtime.c: mem*, __*ti3; the harness: __rust_u128_mulo
# and a bump allocator behind __rust_alloc & co.; every other extern -- the core panic entry
# points, fmt -- is a trapping stub). Compared per call: the outcome class (return / trap
# code / extern / signal), return values, and every memory word the call wrote (argument
# arena incl. pointed-to buffers, heap, writable data objects); bits that depend on
# uninitialised stack/heap bytes (unspecified in CLIF) are not compared. Skipped (and
# counted): timeouts, stack overflows, harness crashes.
#
# Needs dump.sh output (with the crates' objects) and built tools (clif-native,
# clif-data-export, lean-backend).
# usage: scripts/rust-clif/diff-native.sh [OUT_DIR]
#   env: DIFF_WORK (default OUT_DIR/../diff-native), VECTORS (64 per round), MIN_VECTORS (50),
#        MAX_VECTORS (512), PAR (crates in parallel, 6), SEED, CALL_TIMEOUT_MS (500),
#        CRATES (e.g. "release-a_arith debug-i_alloc"; default all)
# Output: DIFF_WORK/<profile>-<crate>.jsonl (one record per function + summary),
#         DIFF_WORK/summary.md (the table), exit status 1 on any disagreement.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
here="$root/scripts/rust-clif"
out=${1:-/tmp/rust-clif-survey/out}
work=${DIFF_WORK:-$out/../diff-native}
VECTORS=${VECTORS:-64}
MIN_VECTORS=${MIN_VECTORS:-50}
MAX_VECTORS=${MAX_VECTORS:-512}
PAR=${PAR:-6}
SEED=${SEED:-24301}
CALL_TIMEOUT_MS=${CALL_TIMEOUT_MS:-500}
native="$root/rust/target/release/clif-native"
backend="$root/.lake/build/bin/lean-backend"
mkdir -p "$work"
ulimit -c 0 # qemu would dump core for every harness crash

exporter="$root/rust/target/release/clif-data-export"
clang --target=aarch64-linux-gnu -ffreestanding -fno-builtin -nostdlib -O1 \
  -c "$here/rust-runtime.c" -o "$work/rust-runtime.o"

crates=${CRATES:-$(for p in debug release release-oc; do for d in "$out/$p"/*/; do
  echo "$p-$(basename "$d")"; done; done)}

one() { # PROFILE-CRATE
  local pc=$1 p c
  case $pc in release-oc-*) p=release-oc ;; release-*) p=release ;; debug-*) p=debug ;; esac
  c=${pc#"$p"-}
  local b="$work/$pc" raw="$out/$p/$c/$c.clif"
  # data image, gv names and the names of the `u0:N` callees (allocator, panics, fmt)
  "$exporter" "$raw" "$out/$p/$c/$c.o" --out "$b.data.clif" --gvmap "$b.gvmap.tsv" \
    --fnmap "$b.fnmap.tsv" >"$b.export.log"
  python3 "$here/normalize.py" "$raw" unopt "$b.clif" \
    --gvmap "$b.gvmap.tsv" --fnmap "$b.fnmap.tsv" --data-file "$b.data.clif"
  "$backend" "$b.clif" "$b.o" --traps "$b.traps.json" >"$b.backend.log" 2>&1
  local rc=0
  "$native" --diff "$b.clif" --lean-obj "$b.o" --lean-table "$b.traps.json" \
    --link "$work/rust-runtime.o" --vectors "$VECTORS" --min-vectors "$MIN_VECTORS" \
    --max-vectors "$MAX_VECTORS" --seed "$SEED" --call-timeout-ms "$CALL_TIMEOUT_MS" --jobs 2 \
    >"$b.jsonl" 2>"$b.err" || rc=$?
  echo "$pc: exit $rc $(tail -1 "$b.jsonl" | python3 -c '
import json, sys
try:
    s = json.load(sys.stdin)["summary"]
    print("functions", s["functions"], "agree", s["agree"], "disagree", s["disagree"], "skipped", s["skipped"], "below-min", s["below_min"])
except Exception as e:
    print("no summary", e)')"
}
export -f one
export work out here exporter native backend VECTORS MIN_VECTORS MAX_VECTORS SEED CALL_TIMEOUT_MS

echo "== clif-native --diff per crate ($PAR in parallel)"
printf '%s\n' $crates | xargs -P "$PAR" -I{} bash -c 'one {}'

python3 - "$work" $crates <<'EOF'
import json, sys, re
from pathlib import Path
from collections import Counter
work, crates = Path(sys.argv[1]), sys.argv[2:]
rows, tot = [], Counter()
disagreements, skipreasons, weakest = [], Counter(), []
classes = Counter()
for pc in crates:
    recs = [json.loads(l) for l in (work / f"{pc}.jsonl").read_text().splitlines() if l.strip()]
    if not recs or "summary" not in recs[-1]:
        err = (work / f"{pc}.err").read_text().strip()
        rows.append(f"| {pc} | ERROR: {err[:200]} |||||||")
        tot["errors"] += 1
        continue
    fns, s = recs[:-1], recs[-1]["summary"]
    log = (work / f"{pc}.backend.log").read_text()
    unverified = len(re.findall(r": compiled, unverified", log))
    exercised = [f["agree"] + f["disagree"] for f in fns]
    vec_min = min(exercised) if exercised else 0
    returned = sum(1 for f in fns if f["outcomes"].get("returned", 0) > 0)
    for f in fns:
        for k, n in f["outcomes"].items():
            classes[re.sub(r" in %.*| _R\S+| u0_\d+", "", k)] += n
        for k, n in f["skipped"].items():
            skipreasons[k] += n
        if f["disagree"]:
            disagreements.append((pc, f["func"], f["examples"][:2]))
        weakest.append((f["agree"] + f["disagree"], pc, f["func"], f["skipped"]))
    sk = sum(s["skipped"].values())
    rows.append(f"| {pc} | {len(fns)} | {len(fns) - unverified} | {s['agree']} | {s['disagree']} | {sk} | "
                f"{vec_min} | {s['below_min']} | {returned} |")
    for k in ("functions", "agree", "disagree", "below_min"):
        tot[k] += s[k]
    tot["verified"] += len(fns) - unverified
    tot["skipped"] += sk
    tot["returned_fns"] += returned
lines = ["| crate | functions | verified | agree (vectors) | disagree | skipped | min vectors/fn | below min | fns returning normally |",
         "|---|---|---|---|---|---|---|---|---|", *rows,
         f"| **total** | {tot['functions']} | {tot['verified']} | {tot['agree']} | {tot['disagree']} | {tot['skipped']} | | "
         f"{tot['below_min']} | {tot['returned_fns']} |", "",
         "Skipped vectors by reason: " + ", ".join(f"{k} {n}" for k, n in skipreasons.most_common()),
         "Agreed outcomes by class: " + ", ".join(f"{k} {n}" for k, n in classes.most_common()), ""]
weakest.sort()
lines.append("Functions with the fewest compared vectors: " +
             ", ".join(f"{pc}:{fn[:40]} {n} {dict(sk)}" for n, pc, fn, sk in weakest[:8]))
for pc, fn, ex in disagreements[:20]:
    lines.append(f"DISAGREE {pc} {fn}: {json.dumps(ex)[:600]}")
(work / "summary.md").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
sys.exit(1 if tot["disagree"] or tot["errors"] else 0)
EOF
