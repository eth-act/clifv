#!/usr/bin/env bash
# End-to-end smoke test of cg_clif CLIF through our pipeline. For scalar corpus functions that
# `lean-backend` compiles (release profile, `nop` kept), attach `; run:` lines whose
# expected values come from the same Rust source compiled by rustc's LLVM backend, then run
#   - clif-filetest (Lean `Clif.run`, compared with Cranelift's interpreter), and
#   - scripts/lean-backend-filetests.sh (Lean backend -> llvm-mc -> qemu, compared with
#     Cranelift's own aarch64 code).
# Needs dump.sh and tools.sh output. usage: scripts/rust-clif/smoke.sh [OUT_DIR]
set -euo pipefail

TOOLCHAIN=${TOOLCHAIN:-nightly-2026-09-26}
root=$(cd "$(dirname "$0")/../.." && pwd)
here="$root/scripts/rust-clif"
out=${1:-/tmp/rust-clif-survey/out}
tools="$out/../tools"
work="$out/../smoke"
rm -rf "$work"
mkdir -p "$work"

externs=()
for c in a_arith c_structs_enums d_loops_iters h_dyn_generic; do
  rustc +"$TOOLCHAIN" --edition 2021 --crate-type rlib --crate-name "$c" -Copt-level=3 \
    -Coverflow-checks=off -Cdebug-assertions=off --out-dir "$work" "$here/corpus/$c.rs"
  externs+=(--extern "$c=$work/lib$c.rlib")
done
rustc +"$TOOLCHAIN" --edition 2021 -Copt-level=1 "${externs[@]}" -o "$work/gen_runs" "$here/smoke/gen_runs.rs"
"$work/gen_runs" >"$work/runs.tsv"

python3 - "$tools" "$work/runs.tsv" "$work/smoke.clif" <<'EOF'
import re, sys
from pathlib import Path
tools, runs, out = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
funcs, header = {}, None
for crate in ("a_arith", "c_structs_enums", "d_loops_iters", "h_dyn_generic"):
    text = (tools / f"release-{crate}.unopt.reader.clif").read_text()
    head, _, rest = text.partition("\nfunction ")
    header = header or head
    for body in ("function " + rest).split("\n\nfunction "):
        body = body if body.startswith("function ") else "function " + body
        name = re.match(r"function %(\S+?)\(", body).group(1)
        funcs[name] = body.rstrip()
lines = {}
for l in open(runs):
    f, r = l.rstrip("\n").split("\t")
    lines.setdefault(f, []).append(r)
order, todo = [], list(lines)
while todo:
    f = todo.pop()
    if f in order:
        continue
    order.append(f)
    todo += re.findall(r"fn\d+ = (?:colocated )?%(\S+?)\(", funcs[f])
parts = [header.rstrip()]
for f in sorted(order):
    parts.append(funcs[f] + "".join("\n" + r for r in lines.get(f, [])))
Path(out).write_text("\n\n".join(parts) + "\n")
print(f"smoke.clif: {len(order)} functions, {sum(map(len, lines.values()))} run lines")
EOF

cd "$root"
echo "== clif-filetest (Lean Clif.run vs Cranelift interpreter)"
rust/target/release/clif-oracle interp "$work/smoke.clif" >"$work/oracle.jsonl" || true
.lake/build/bin/clif-filetest --oracle "$work/oracle.jsonl" "$work/smoke.clif" || true
echo "== lean-backend-filetests (Lean backend on qemu vs Cranelift aarch64 on qemu)"
scripts/lean-backend-filetests.sh -v "$work/smoke.clif"
