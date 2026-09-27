#!/usr/bin/env bash
# Performance metrics of the Lean backend (docs/contracts/regalloc.md, PLAN.md M6 exit:
# "performance is measured against both Cranelift and the stack-slot baseline").
#
# 1. Code size per corpus file (bytes of all functions of the file) for the Lean backend with
#    the stack-slot allocator, with regalloc2, and for Cranelift 0.136.1 (clif2obj's settings,
#    opt_level=none; the size of each function's dumped code), plus totals.
# 2. Executed instructions (dynamic count) on the Lean Arm model for the corpus functions
#    `lean-backend-armrun` can run (no calls, no memory), summed over each function's run
#    lines, for the same three code generators (`lean-backend-armrun --regalloc stack`,
#    `--regalloc regalloc2`, and `--bins` with Cranelift's dumped code).
#
# usage: scripts/lean-backend-metrics.sh [FILE.clif...]   (default: corpus/clif/*.clif)
# Output: two markdown tables on stdout.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
FILES=("$@")
if [[ ${#FILES[@]} -eq 0 ]]; then FILES=(corpus/clif/*.clif); fi

lake build lean-backend lean-backend-armrun >/dev/null
cargo build --quiet --release --manifest-path rust/Cargo.toml -p lean-regalloc -p clif2obj

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

for f in "${FILES[@]}"; do
  b=$(basename "$f" .clif)
  mkdir -p "$WORK/$b/cl"
  .lake/build/bin/lean-backend "$f" "$WORK/$b/stack.o" --regalloc stack --traps "$WORK/$b/stack.json" 2>/dev/null
  .lake/build/bin/lean-backend "$f" "$WORK/$b/ra.o" --regalloc regalloc2 --traps "$WORK/$b/ra.json" 2>/dev/null
  rust/target/release/clif2obj "$f" aarch64-unknown-linux-gnu "$WORK/$b/cl.o" "$WORK/$b/cl" >/dev/null 2>&1 || true
done

python3 - "$WORK" "${FILES[@]}" <<'EOF'
import json, os, sys
work, files = sys.argv[1], sys.argv[2:]
print("| file | functions | stack | regalloc2 | Cranelift | regalloc2 / Cranelift | stack / regalloc2 |")
print("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
tot = [0, 0, 0, 0]
for f in files:
    b = os.path.basename(f)[:-5]
    st = {x["name"]: x["size"] for x in json.load(open(f"{work}/{b}/stack.json"))["functions"]}
    ra = {x["name"]: x["size"] for x in json.load(open(f"{work}/{b}/ra.json"))["functions"]}
    names = sorted(set(st) & set(ra))
    cl = {}
    for n in names:
        p = f"{work}/{b}/cl/{n}.bin"
        if os.path.exists(p): cl[n] = os.path.getsize(p)
    names = [n for n in names if n in cl]
    if not names: continue
    s, r, c = (sum(d[n] for n in names) for d in (st, ra, cl))
    tot = [tot[0] + len(names), tot[1] + s, tot[2] + r, tot[3] + c]
    print(f"| {b} | {len(names)} | {s} | {r} | {c} | {r / c:.2f} | {s / r:.2f} |")
n, s, r, c = tot
print(f"| **total** | {n} | **{s}** | **{r}** | **{c}** | **{r / c:.2f}** | **{s / r:.2f}** |")
EOF

echo
armrun() { .lake/build/bin/lean-backend-armrun "$@" | grep -E '^%' | sed -E 's/^%([^:]+): ([0-9]+) instructions, ([0-9]+) runs agree, ([0-9]+) executed$/\1 \2 \3 \4/' || true; }
for f in "${FILES[@]}"; do
  b=$(basename "$f" .clif)
  armrun --regalloc stack "$f" >> "$WORK/dyn.stack"
  armrun --regalloc regalloc2 "$f" >> "$WORK/dyn.ra"
  armrun --bins "$WORK/$b/cl" "$f" >> "$WORK/dyn.cl"
done
python3 - "$WORK" <<'EOF'
import sys
work = sys.argv[1]
def load(p):
    d = {}
    for line in open(p):
        parts = line.split()
        if len(parts) == 4 and parts[3].isdigit(): d[parts[0]] = (int(parts[2]), int(parts[3]))
    return d
st, ra, cl = (load(f"{work}/dyn.{k}") for k in ("stack", "ra", "cl"))
print("| function | runs | stack | regalloc2 | Cranelift | regalloc2 / Cranelift | stack / regalloc2 |")
print("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
tot = [0, 0, 0]
for n in sorted(set(st) & set(ra) & set(cl)):
    (k, s), (_, r), (kc, c) = st[n], ra[n], cl[n]
    if k != kc or c == 0: continue
    tot = [tot[0] + s, tot[1] + r, tot[2] + c]
    print(f"| {n} | {k} | {s} | {r} | {c} | {r / c:.2f} | {s / r:.2f} |")
s, r, c = tot
print(f"| **total** | | **{s}** | **{r}** | **{c}** | **{r / c:.2f}** | **{s / r:.2f}** |")
EOF
