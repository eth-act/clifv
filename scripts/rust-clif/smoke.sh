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

# ---- data-image demos (rust-route step 1): functions whose only inputs are the
# recovered `; data:` objects ----
# `%ksum` sums K[0..8] of SHA-256 from the recovered constant table via symbol_value +
# loads; `%memrot` stores/reads a writable recovered object; `%sha256_compress` (the real
# cg_clif function, pointers unused here) links the whole data image. Expected values come
# from the same constants compiled by rustc's LLVM backend.
if [[ "${1:-}" != "--no-data" ]]; then
  here_d="$here/smoke-data"
  rm -rf "$here_d"; mkdir -p "$here_d"
  cat >"$here_d/expect.rs" <<'RUST'
// Expected values for the data-image demos (rustc/LLVM is the oracle).
const K: [u32; 64] = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
fn main() {
    let mut sum = 0u64;
    for i in 0..8 { sum += K[i] as u64; }
    println!("{}", sum as u32);
    println!("{}", 0x12345678u32.rotate_left(7));
    println!("{}", 1u32.rotate_left(7));
}
RUST
  rustc -O "$here_d/expect.rs" -o "$here_d/expect" 2>"$here_d/expect.err" || {
    cat "$here_d/expect.err"; exit 1; }
  mapfile -t E < <("$here_d/expect")

  # recover + normalize the release f_crypto crate with its data image
  "$root/scripts/rust-clif/data-export.sh" >/dev/null || exit 1
  datadir="$out/../data"
  python3 "$here/normalize.py" "$out/release/f_crypto/f_crypto.clif" unopt \
    "$here_d/f_crypto.norm.clif" --gvmap "$datadir/release-f_crypto.gvmap.tsv" \
    --data-file "$datadir/release-f_crypto.data.clif"

  python3 - "$here_d" "${E[0]}" "${E[1]}" "${E[2]}" <<'PYEOF'
import re, sys
from pathlib import Path
d, ksum, rot, rot1 = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
src = (Path(d) / "f_crypto.norm.clif").read_text()
lines = src.splitlines()
starts = [(i, l) for i, l in enumerate(lines) if l.startswith("function %")]
sha = next(i for i, l in starts if l.startswith("function %sha256_compress"))
end = next((i for i, l in starts if i > sha), len(lines))
sha_body = "\n".join(lines[sha:end])
data_lines = [l for l in lines[:starts[0][0]] if l.startswith("; data:")]
buf = "; data: %demo_buf writable = " + "0" * 32
ksum_fn = f'''function %ksum() -> i32 system_v {{
    gv0 = symbol colocated %f_crypto_Ldata40

block0:
    v1 = iconst.i64 0
    v2 = iconst.i64 0
    v19 = iconst.i64 8
    v20 = iconst.i64 4
    jump block1(v1, v2)

block1(v3: i64, v4: i64):
    v5 = icmp ult v4, v19
    brif v5, block2(v3, v4), block4(v3)

block2(v6: i64, v7: i64):
    v9 = imul.i64 v7, v20
    v10 = symbol_value.i64 gv0
    v11 = iadd.i64 v10, v9
    v12 = load.i32 notrap aligned v11
    v13 = uextend.i64 v12
    v14 = iadd.i64 v6, v13
    v15 = iconst.i64 1
    v16 = iadd.i64 v7, v15
    jump block1(v14, v16)

block4(v17: i64):
    v18 = ireduce.i32 v17
    return v18
}}

; run: %ksum() == {ksum}
'''
rot_fn = f'''function %memrot(i32) -> i32 system_v {{
    gv0 = symbol colocated %demo_buf

block0(v0: i32):
    v1 = symbol_value.i64 gv0
    store.i32 notrap aligned v0, v1
    v2 = load.i32 notrap aligned v1
    v4 = iconst.i32 7
    v3 = rotl.i32 v2, v4
    return v3
}}

; run: %memrot(305419896) == {rot}
; run: %memrot(1) == {rot1}
'''
out = "\n".join(data_lines + [buf]) + "\n\n" + ksum_fn + "\n" + rot_fn + "\n" + sha_body + "\n"
(Path(d) / "data.clif").write_text(out)
print(f"data.clif: 3 functions, 3 run lines (expected from rustc/LLVM)")
PYEOF

  echo "== clif-filetest (Lean Clif.run with the link-time image)"
  .lake/build/bin/clif-filetest "$here_d/data.clif"
  echo "== lean-backend-filetests (Lean backend on qemu)"
  scripts/lean-backend-filetests.sh "$here_d/data.clif"
fi
