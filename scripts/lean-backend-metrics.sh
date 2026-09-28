#!/usr/bin/env bash
# Performance metrics of the Lean backend and mid-end (docs/contracts/regalloc.md, PLAN.md M6
# exit: "performance is measured against both Cranelift and the stack-slot baseline";
# docs/contracts/midend.md "Results").
#
# Five code generators:
#   stack    Lean backend, stack-slot allocator (no mid-end)
#   ra       Lean backend, regalloc2 (no mid-end)
#   ra+opt   Lean mid-end (Opt.optimize) + Lean backend, regalloc2 (`lean-backend --opt`)
#   cl       Cranelift 0.136.1, clif2obj's settings (opt_level=none)
#   cl-speed Cranelift 0.136.1, the same settings but opt_level=speed (`clif2obj --opt-level speed`)
#
# 1. Code size per corpus file (bytes of all functions of the file; Cranelift: the size of each
#    function's dumped code), plus totals.
# 2. Executed instructions (dynamic count) on the Lean Arm model for the corpus functions
#    `lean-backend-armrun` can run (no calls, no memory), summed over each function's run
#    lines (`lean-backend-armrun --regalloc stack|regalloc2 [--opt]`, and `--bins` with
#    Cranelift's dumped code).
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
  mkdir -p "$WORK/$b/cl" "$WORK/$b/clsp"
  .lake/build/bin/lean-backend "$f" "$WORK/$b/stack.o" --regalloc stack --traps "$WORK/$b/stack.json" 2>/dev/null
  .lake/build/bin/lean-backend "$f" "$WORK/$b/ra.o" --regalloc regalloc2 --traps "$WORK/$b/ra.json" 2>/dev/null
  .lake/build/bin/lean-backend "$f" "$WORK/$b/raopt.o" --regalloc regalloc2 --opt ${METRICS_OPT:-} --traps "$WORK/$b/raopt.json" 2>/dev/null
  rust/target/release/clif2obj "$f" aarch64-unknown-linux-gnu "$WORK/$b/cl.o" "$WORK/$b/cl" >/dev/null 2>&1 || true
  rust/target/release/clif2obj --opt-level speed "$f" aarch64-unknown-linux-gnu "$WORK/$b/clsp.o" "$WORK/$b/clsp" >/dev/null 2>&1 || true
done

python3 - "$WORK" "${FILES[@]}" <<'EOF'
import json, os, sys
work, files = sys.argv[1], sys.argv[2:]
cols = ["stack", "ra", "raopt", "cl", "clsp"]
print("| file | functions | stack | regalloc2 | regalloc2+opt | Cranelift none | Cranelift speed | ra+opt / ra | ra+opt / Cl speed | ra / Cl none |")
print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
tot = {c: 0 for c in cols}; nf = 0
for f in files:
    b = os.path.basename(f)[:-5]
    d = {}
    for c in ("stack", "ra", "raopt"):
        d[c] = {x["name"]: x["size"] for x in json.load(open(f"{work}/{b}/{c}.json"))["functions"]}
    for c in ("cl", "clsp"):
        d[c] = {}
        for n in d["ra"]:
            p = f"{work}/{b}/{c}/{n}.bin"
            if os.path.exists(p): d[c][n] = os.path.getsize(p)
    names = sorted(set.intersection(*(set(d[c]) for c in cols)))
    if not names: continue
    s = {c: sum(d[c][n] for n in names) for c in cols}
    nf += len(names)
    for c in cols: tot[c] += s[c]
    print(f"| {b} | {len(names)} | {s['stack']} | {s['ra']} | {s['raopt']} | {s['cl']} | {s['clsp']} | "
          f"{s['raopt'] / s['ra']:.2f} | {s['raopt'] / s['clsp']:.2f} | {s['ra'] / s['cl']:.2f} |")
t = tot
print(f"| **total** | {nf} | **{t['stack']}** | **{t['ra']}** | **{t['raopt']}** | **{t['cl']}** | **{t['clsp']}** | "
      f"**{t['raopt'] / t['ra']:.2f}** | **{t['raopt'] / t['clsp']:.2f}** | **{t['ra'] / t['cl']:.2f}** |")
EOF

echo
armrun() { .lake/build/bin/lean-backend-armrun "$@" | grep -E '^%' | sed -E 's/^%([^:]+): ([0-9]+) instructions, ([0-9]+) runs agree, ([0-9]+) executed$/\1 \2 \3 \4/' || true; }
for f in "${FILES[@]}"; do
  b=$(basename "$f" .clif)
  armrun --regalloc stack "$f" >> "$WORK/dyn.stack"
  armrun --regalloc regalloc2 "$f" >> "$WORK/dyn.ra"
  armrun --regalloc regalloc2 --opt ${METRICS_OPT:-} "$f" >> "$WORK/dyn.raopt"
  armrun --bins "$WORK/$b/cl" "$f" >> "$WORK/dyn.cl"
  armrun --bins "$WORK/$b/clsp" "$f" >> "$WORK/dyn.clsp"
done
python3 - "$WORK" <<'EOF'
import sys
work = sys.argv[1]
cols = ["stack", "ra", "raopt", "cl", "clsp"]
def load(p):
    d = {}
    for line in open(p):
        parts = line.split()
        if len(parts) == 4 and parts[3].isdigit(): d[parts[0]] = (int(parts[2]), int(parts[3]))
    return d
d = {c: load(f"{work}/dyn.{c}") for c in cols}
print("| function | runs | stack | regalloc2 | regalloc2+opt | Cranelift none | Cranelift speed | ra+opt / ra | ra+opt / Cl speed | ra / Cl none |")
print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
tot = {c: 0 for c in cols}
for n in sorted(set.intersection(*(set(d[c]) for c in cols))):
    k = d["ra"][n][0]
    if any(d[c][n][0] != k or d[c][n][1] == 0 for c in cols): continue
    s = {c: d[c][n][1] for c in cols}
    for c in cols: tot[c] += s[c]
    print(f"| {n} | {k} | {s['stack']} | {s['ra']} | {s['raopt']} | {s['cl']} | {s['clsp']} | "
          f"{s['raopt'] / s['ra']:.2f} | {s['raopt'] / s['clsp']:.2f} | {s['ra'] / s['cl']:.2f} |")
t = tot
print(f"| **total** | | **{t['stack']}** | **{t['ra']}** | **{t['raopt']}** | **{t['cl']}** | **{t['clsp']}** | "
      f"**{t['raopt'] / t['ra']:.2f}** | **{t['raopt'] / t['clsp']:.2f}** | **{t['ra'] / t['cl']:.2f}** |")
EOF
