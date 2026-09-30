#!/usr/bin/env bash
# Byte-for-byte check of the Lean encoder (FV/Backend/{Encode,Obj}.lean,
# docs/contracts/encoder.md) against llvm-mc, the test oracle.
#
# For each .clif file: `lean-backend F.clif F.s` (assembly of the final instruction list) and
# `lean-backend F.clif F.o` (the same list encoded by Lean, ELF object written by Lean);
# `llvm-mc F.s` -> F.mc.o. Per compiled function, compare exactly:
#   - the .text bytes of the function symbol's range,
#   - the relocations in that range (offset, type, symbol name, addend),
#   - the function symbol (value, size, type, binding),
# and per file the mapping symbols ($x/$d kind and value) and the set of undefined symbols.
#
# usage: scripts/lean-backend-encode-check.sh [-v] [--regalloc regalloc2|stack]
#                                             [--corpus | --runtests | --random |
#                                             --n N | --seed S | FILE.clif...]
#   default: --corpus (corpus/clif/*.clif, corpus/clif/extrt/*.clif, corpus/clif-regress/*.clif), --runtests
#   (every file of Cranelift's runtests/; functions outside E are not compiled) and --random
#   (`lean-backend-encode-test random`: every Insn form with N random operand sets
#   (default 200, seed S default 0x5eed = 24301), one function per form; it also runs the
#   decode check on them)
# Output: one line per differing function (every function with -v), then totals.
# Exit status 0 iff every compiled function is identical and no file fails.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
RUNTESTS=third_party/wasmtime/cranelift/filetests/filetests/runtests
LLVM_MC=${LLVM_MC:-/usr/lib/llvm-18/bin/llvm-mc}

VERBOSE=0
RA=regalloc2
FILES=()
SETS=()
N=200
SEED=24301
while [[ $# -gt 0 ]]; do
  case "$1" in
    -v) VERBOSE=1 ;;
    --regalloc) RA=$2; shift ;;
    --corpus) SETS+=(corpus) ;;
    --runtests) SETS+=(runtests) ;;
    --random) SETS+=(random) ;;
    --n) N=$2; shift ;;
    --seed) SEED=$2; shift ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) FILES+=("$1") ;;
  esac
  shift
done
if [[ ${#SETS[@]} -eq 0 && ${#FILES[@]} -eq 0 ]]; then SETS=(corpus runtests random); fi
for s in "${SETS[@]}"; do
  case "$s" in
    corpus) FILES+=(corpus/clif/*.clif corpus/clif/extrt/*.clif corpus/clif-regress/*.clif) ;;
    runtests) FILES+=("$RUNTESTS"/*.clif) ;;
    random) FILES+=(@random) ;;
  esac
done

echo "== build"
lake build lean-backend lean-backend-encode-test 2>&1 | tail -1
cargo build --quiet --release --manifest-path rust/Cargo.toml -p lean-regalloc

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

one() {
  local f=$1 b
  # fullfp16 only for `fmov h, w` (random forms); it changes no other encoding
  local MC_FLAGS=(-triple=aarch64-linux-gnu -mattr=+fullfp16 -filetype=obj)
  b=$(printf '%s' "$f" | tr '/' '_')
  b=${b%.clif}
  if [[ $f == @random ]]; then
    if ! .lake/build/bin/lean-backend-encode-test random "$WORK/$b.s" "$WORK/$b.o" --n "$N" \
         --seed "$SEED" > "$WORK/$b.log" 2> "$WORK/$b.err"; then
      cat "$WORK/$b.log" >> "$WORK/$b.err"
      echo "lean-encode-failed" > "$WORK/$b.status"; return 0
    fi
  else
    .lake/build/bin/lean-backend "$f" "$WORK/$b.s" --regalloc "$RA" 2>/dev/null
    if ! .lake/build/bin/lean-backend "$f" "$WORK/$b.o" --regalloc "$RA" 2> "$WORK/$b.err"; then
      echo "lean-encode-failed" > "$WORK/$b.status"; return 0
    fi
  fi
  if ! "$LLVM_MC" "${MC_FLAGS[@]}" "$WORK/$b.s" -o "$WORK/$b.mc.o" 2> "$WORK/$b.mcerr"; then
    echo "llvm-mc-failed" > "$WORK/$b.status"; return 0
  fi
  echo ok > "$WORK/$b.status"
}
export -f one
export WORK LLVM_MC N SEED RA
printf '%s\0' "${FILES[@]}" | xargs -0 -n1 -P "$(nproc)" bash -c 'one "$1"' _

python3 - "$WORK" "$VERBOSE" "${FILES[@]}" <<'EOF'
import os, struct, sys
work, verbose, files = sys.argv[1], sys.argv[2] == "1", sys.argv[3:]
RT = {283: "CALL26", 311: "ADR_GOT_PAGE", 312: "LD64_GOT_LO12_NC", 275: "ADR_PREL_PG_HI21",
      277: "ADD_ABS_LO12_NC"}

def elf(path):
    d = open(path, "rb").read()
    shoff, = struct.unpack_from("<Q", d, 0x28)
    shnum, shstrndx = struct.unpack_from("<HH", d, 0x3c)
    secs = []
    for i in range(shnum):
        name, typ, flags, addr, off, size, link, info, align, ent = \
            struct.unpack_from("<IIQQQQIIQQ", d, shoff + 64 * i)
        secs.append(dict(name=name, type=typ, off=off, size=size, link=link, info=info))
    shs = secs[shstrndx]
    def nm(tab, o):
        e = d.index(b"\0", tab["off"] + o)
        return d[tab["off"] + o:e].decode()
    for s in secs: s["n"] = nm(shs, s["name"])
    text_i = [i for i, s in enumerate(secs) if s["n"] == ".text"][0]
    text = d[secs[text_i]["off"]:secs[text_i]["off"] + secs[text_i]["size"]]
    symtab = [s for s in secs if s["type"] == 2][0]
    strtab = secs[symtab["link"]]
    syms = []
    for i in range(symtab["size"] // 24):
        name, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", d, symtab["off"] + 24 * i)
        syms.append(dict(name=nm(strtab, name), bind=info >> 4, type=info & 15, shndx=shndx,
                         value=value, size=size))
    relocs = []
    for s in secs:
        if s["type"] == 4 and s["info"] == text_i:
            for i in range(s["size"] // 24):
                off, info, add = struct.unpack_from("<QQq", d, s["off"] + 24 * i)
                relocs.append((off, RT.get(info & 0xffffffff, info & 0xffffffff),
                               syms[info >> 32]["name"], add))
    funcs = {s["name"]: s for s in syms if s["type"] == 2}
    maps = sorted((s["value"], s["name"][:2]) for s in syms if s["name"][:2] in ("$x", "$d"))
    undef = sorted(s["name"] for s in syms if s["shndx"] == 0 and s["name"])
    return text, funcs, sorted(relocs), maps, undef

T = dict(files=0, nofuncs=0, fail_files=0, funcs=0, same=0, differ=0, words=0, relocs=0)
for f in files:
    b = f.replace("/", "_")
    if b.endswith(".clif"): b = b[:-5]
    st = open(os.path.join(work, b + ".status")).read().strip()
    T["files"] += 1
    if st != "ok":
        T["fail_files"] += 1
        err = open(os.path.join(work, b + (".err" if st == "lean-encode-failed" else ".mcerr"))).read()
        print(f"{f}: {st}: {err.strip()[:400]}")
        continue
    lt, lf, lr, lm, lu = elf(os.path.join(work, b + ".o"))
    mt, mf, mr, mm, mu = elf(os.path.join(work, b + ".mc.o"))
    if not lf and not mf:
        T["nofuncs"] += 1
    file_bad = []
    if lm != mm: file_bad.append(f"mapping symbols differ: lean {lm[:6]} llvm-mc {mm[:6]}")
    if lu != mu: file_bad.append(f"undefined symbols differ: lean {lu} llvm-mc {mu}")
    if set(lf) != set(mf): file_bad.append(f"function sets differ: {sorted(set(lf) ^ set(mf))}")
    if len(lt) != len(mt): file_bad.append(f".text size {len(lt)} vs {len(mt)}")
    if file_bad:
        T["fail_files"] += 1
        for m in file_bad: print(f"{f}: {m}")
    for name in sorted(set(lf) & set(mf)):
        a, m = lf[name], mf[name]
        T["funcs"] += 1
        diffs = []
        for k in ("value", "size", "bind", "type"):
            if a[k] != m[k]: diffs.append(f"symbol {k} {a[k]} vs {m[k]}")
        lo, hi = m["value"], m["value"] + m["size"]
        la, ma = lt[a["value"]:a["value"] + a["size"]], mt[lo:hi]
        if la != ma:
            for i in range(0, min(len(la), len(ma)), 4):
                if la[i:i+4] != ma[i:i+4]:
                    lw, = struct.unpack_from("<I", la, i); mw, = struct.unpack_from("<I", ma, i)
                    diffs.append(f"word +{i}: lean {lw:08x} llvm-mc {mw:08x}")
                    break
            else:
                diffs.append("text length differs")
        rl = [(o - a["value"], t, s, ad) for (o, t, s, ad) in lr if a["value"] <= o < a["value"] + a["size"]]
        rm = [(o - lo, t, s, ad) for (o, t, s, ad) in mr if lo <= o < hi]
        if rl != rm: diffs.append(f"relocs lean {rl} llvm-mc {rm}")
        T["words"] += len(ma) // 4
        T["relocs"] += len(rm)
        if diffs:
            T["differ"] += 1
            print(f"{f}: %{name}: DIFFER: " + "; ".join(diffs))
        else:
            T["same"] += 1
            if verbose: print(f"{f}: %{name}: identical ({len(ma)} bytes, {len(rm)} relocs)")
print(f"files {T['files']} (with no compiled function {T['nofuncs']}, failing {T['fail_files']}); "
      f"functions {T['funcs']}: identical {T['same']}, differ {T['differ']}; "
      f"{T['words']} words, {T['relocs']} relocations compared")
sys.exit(0 if T["differ"] == 0 and T["fail_files"] == 0 else 1)
EOF
