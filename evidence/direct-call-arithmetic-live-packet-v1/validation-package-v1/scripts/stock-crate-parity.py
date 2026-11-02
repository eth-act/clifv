#!/usr/bin/env python3
"""Per-function byte comparison of a crate's Lean-compiled code with stock Cranelift's (cg_clif).

`cargo fv test --keep-temps` keeps, per codegen unit, cg_clif's object (`cgclif.o`, stock
Cranelift's code) and the Lean backend's object (`lean.o`) under `target/fv/<mode>/tmp/<cgu>/`.
For every function of `lean.o` this compares its bytes and relocations with the same symbol in
`cgclif.o` (exact, no normalisation) and, for differing functions, attributes the differing
instructions to causes (heuristic, on `llvm-mc` disassembly; the counts are instruction lines):

  frame           prologue/epilogue/callee-save code (`stp x29, x30`, `sub/add sp`, saves of x19-x28/d8-d15)
  slot-layout     same instruction, different `[sp, #off]` (stack/spill slot placement), `mov xN, sp` vs `add xN, sp, #k`
  regalloc        same instruction, different registers; extra/missing register moves, spills, reloads
  dead-cmp-cset   Lean's unused `cset` of a compare whose user compares again (`cmp; cset; cmp; b.c`)
  dead-other      other Lean-only results that are overwritten before being read
  branch-layout   branch-only hunks (jumps to the next block, inverted branches), reordered blocks
  branch-offsets  same branch, different offset (a consequence of the other causes)
  constants       same instruction, different immediate
  isel-*          other instruction-selection differences (extend, symaddr, const, other)

usage: scripts/stock-crate-parity.py [--json OUT.json] [--diffs DIR] TMPDIR...
  TMPDIR: `target/fv/<mode>/tmp` of a `cargo fv test --keep-temps` run (or single CGU dirs).
"""
import argparse
from collections import Counter
import difflib
import json
from pathlib import Path
import re
import subprocess

from byte_compare import ELF

MC = "/usr/lib/llvm-18/bin/llvm-mc"


def disasm(data):
    words = " ".join("0x%02x" % b for b in data)
    p = subprocess.run([MC, "--disassemble", "-triple=aarch64", "-mattr=+lse,+fp-armv8,+neon"],
                       input=words, capture_output=True, text=True)
    out = []
    for line in p.stdout.splitlines():
        t = line.strip()
        if t and not t.startswith("."):
            out.append(re.sub(r"\s+", " ", t.split("//")[0]).strip())
    return out


CS = re.compile(r"\b(x(19|2[0-8])|d(8|9|1[0-5]))\b")


def is_frame(i):
    op = i.split(" ")[0]
    if re.match(r"(stp|ldp) x29, x30", i) or i == "mov x29, sp":
        return True
    if re.match(r"(sub|add) sp, sp, #", i):
        return True
    if op in ("str", "ldr", "stp", "ldp", "stur", "ldur") and "sp" in i and CS.search(i.split("[")[0]):
        return True
    return False


def split(asm):
    frame = [i for i in asm if is_frame(i)]
    body = [i for i in asm if not is_frame(i) and i != "ret"]
    return frame, body


def opcode(i):
    return i.split(" ")[0]


def canon_regs(seq):
    m = {}
    out = []
    for i in seq:
        def r(mo):
            name = mo.group(0)
            if name in ("sp", "xzr", "wzr", "x29", "x30"):
                return name
            num = re.sub(r"^[xwdsqbhv]", "", name)
            k = m.setdefault(num, "R%d" % len(m))
            return name[0] + k
        out.append(re.sub(r"\b([xwdsqbhv]\d+|sp|xzr|wzr)\b", r, i))
    return out


def no_imm(seq):
    return [re.sub(r"#-?(0x)?[0-9a-f]+", "#I", i) for i in seq]


REG = re.compile(r"\b([xw](\d+)|sp|xzr|wzr|[dsqv](\d+))\b")
NOWRITE = ("str", "stur", "stp", "strb", "strh", "sturb", "sturh", "cmp", "cmn", "tst", "b", "bl", "br", "blr",
           "ret", "cbz", "cbnz", "tbz", "tbnz", "udf", "fcmp", "ccmp", "stlr", "stlrb", "stlrh", "stxr")


def regs(i):
    return [m.group(0) for m in REG.finditer(i.split(" ", 1)[1])] if " " in i else []


def key(r):
    m = re.match(r"[xw](\d+)$", r)
    if m: return "x" + m[1]
    m = re.match(r"[dsqv](\d+)$", r)
    if m: return "v" + m[1]
    return r


def dest(i):
    op = i.split(" ")[0]
    if op in NOWRITE or op.startswith("b."):
        return None
    rs = regs(i)
    return key(rs[0]) if rs else None


def is_branch(i):
    op = i.split(" ")[0]
    return op in ("b", "br", "ret", "cbz", "cbnz", "tbz", "tbnz", "blr", "bl") or op.startswith("b.")


def dead(seq, k):
    d = dest(seq[k])
    if d is None or d in ("sp", "xzr"):
        return False
    for j in range(k + 1, len(seq)):
        i = seq[j]
        if is_branch(i):
            return False
        rs = [key(r) for r in regs(i)]
        dj = dest(i)
        reads = rs[1:] if dj is not None else rs
        if d in reads:
            return False
        if dj == d:
            return True
        # flag-setting cset reads flags only; fine
    return False


def norm_sp(i):
    return re.sub(r"\[sp, #-?\d+\]|\[sp\]", "[sp,#O]", re.sub(r"add (\w+), sp, #\d+", r"add \1, sp, #O", i))


BR = lambda o: o in ("b", "cbz", "cbnz", "tbz", "tbnz", "udf") or o.startswith("b.")


def strip_regs(i):
    return re.sub(r"\b[xwdsqv]\d+\b", "r", i)


def hunk_cause(sa, la, lean, j1):
    """sa: stock-only insns, la: lean-only insns (with positions j1.. in lean body)."""
    so = [opcode(i) for i in sa]
    lo = [opcode(i) for i in la]
    deadflags = [dead(lean, j1 + k) for k in range(len(la))]
    # Lean's `cmp a, b; cset t, c; cmp a, b; b.c`: the boolean of an icmp whose user re-compares
    for k, i in enumerate(la):
        p = j1 + k
        if opcode(i) == "cset" and p > 0 and p + 1 < len(lean) and opcode(lean[p - 1]) in ("cmp", "tst", "cmn") \
                and lean[p + 1] == lean[p - 1]:
            deadflags[k] = True
        elif opcode(i) == "cset" and p + 1 < len(lean) and (BR(opcode(lean[p + 1])) or opcode(lean[p + 1]) in ("cmp", "tst")) \
                and key(regs(i)[0]) not in [key(r) for r in regs(lean[p + 1])]:
            deadflags[k] = True
    alive = [i for i, d in zip(la, deadflags) if not d]
    ao = [opcode(i) for i in alive]
    causes = Counter()
    if any(d and opcode(i) == "cset" for i, d in zip(la, deadflags)):
        causes["dead-cmp-cset"] += sum(1 for i, d in zip(la, deadflags) if d and opcode(i) == "cset")
        # the duplicated cmp before the branch is part of the same mechanism
        n = sum(1 for o in ao if o == "cmp")
        causes["dead-cmp-cset"] += n
        alive = [i for i in alive if opcode(i) != "cmp"]
        ao = [opcode(i) for i in alive]
    nd = sum(1 for i, d in zip(la, deadflags) if d and opcode(i) != "cset")
    if nd:
        causes["dead-other"] += nd
    if not so and not ao:
        return causes
    if all(BR(o) for o in so + ao):
        causes["branch-layout"] += max(len(so), len(ao))
    elif all(o in ("mov", "ldur", "stur", "ldr", "str") and not re.search(r"#(?!0x)", i) or o == "mov" and re.match(r"mov [xw]\d+, [xw]\d+$", i)
             for o, i in zip(so + ao, sa + alive)) and all(re.match(r"mov [xw]\d+, [xw]\d+$", i) or "sp" in i for i in sa + alive):
        causes["regalloc"] += max(len(so), len(ao))
    elif Counter(so) == Counter(ao) or (len(so) + len(ao) >= 6 and
            sum((Counter(so) & Counter(ao)).values()) * 2 >= 0.6 * (len(so) + len(ao))):
        causes["branch-layout"] += max(len(so), len(ao))
    else:
        sub = "isel-other"
        if set(so + ao) <= {"uxtb", "uxth", "sxtb", "sxth", "sxtw", "and"}:
            sub = "isel-extend"
        elif set(so + ao) <= {"adrp", "ldr"} and "adrp" in so + ao:
            sub = "isel-symaddr"
        elif all(re.match(r"(mov|movz|movk|movn) [xw]\d+, #", i) for i in sa + alive):
            sub = "isel-const"
        causes[sub] += max(len(so), len(ao))
    return causes


def analyse(a, b):
    causes = Counter()
    fa, ba = split(a)
    fb, bb = split(b)
    if fa != fb:
        causes["frame"] += max(len(fa), len(fb))
    oa = [opcode(i) for i in ba]
    ob = [opcode(i) for i in bb]
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, oa, ob, autojunk=False).get_opcodes():
        if tag == "equal":
            for x, y in zip(ba[i1:i2], bb[j1:j2]):
                if x == y:
                    continue
                if [key(r) for r in regs(x)] != [key(r) for r in regs(y)]:
                    causes["regalloc"] += 1
                sx, sy = strip_regs(x), strip_regs(y)
                if sx != sy:
                    if norm_sp(sx) == norm_sp(sy) and ("sp" in x):
                        causes["slot-layout"] += 1
                    elif BR(opcode(x)) or opcode(x) == "adr":
                        causes["branch-offsets"] += 1
                    else:
                        causes["constants"] += 1
        else:
            sa, la = ba[i1:i2], bb[j1:j2]
            # `mov xN, sp` (stock, slot at sp+0) vs `add xN, sp, #k` (Lean): slot layout
            if len(sa) == len(la) and all(re.match(r"mov \w+, sp$", s) and re.match(r"add \w+, sp, #\d+$", l) for s, l in zip(sa, la)):
                causes["slot-layout"] += len(sa)
                continue
            causes.update(hunk_cause(sa, la, bb, j1))
    return causes



def cgu_dirs(paths):
    for p in map(Path, paths):
        if (p / "lean.o").exists():
            yield p
        else:
            yield from sorted(d for d in p.iterdir() if (d / "lean.o").exists() and (d / "cgclif.o").exists())


def compare(paths, diffs=None):
    rows = []
    for d in cgu_dirs(paths):
        lean, cg = ELF(d / "lean.o"), ELF(d / "cgclif.o")
        for name, syms in sorted(lean.functions.items()):
            if len(syms) != 1 or not syms[0]["size"]:
                continue
            ls, lb = lean.function(name)
            try:
                cs, cb = cg.function(name)
            except ValueError as e:
                rows.append({"cgu": d.name, "fn": name, "error": str(e)})
                continue
            rel = lambda elf, s: [(r["offset"], r["type"], r["addend"]) for r in elf.function_relocations(s, {})]
            row = {"cgu": d.name, "fn": name, "stock": len(cb), "lean": len(lb),
                   "equal": lb == cb and rel(lean, ls) == rel(cg, cs)}
            if not row["equal"]:
                a, b = disasm(cb), disasm(lb)
                row["causes"] = dict(analyse(a, b)) or {"relocations": 1}
                if diffs:
                    Path(diffs).mkdir(parents=True, exist_ok=True)
                    (Path(diffs) / f"{d.name}_{name[:150]}.diff").write_text(
                        "\n".join(difflib.unified_diff(a, b, "stock", "lean", lineterm="", n=2)) + "\n")
            rows.append(row)
    return rows


def summary(rows):
    ok = [r for r in rows if "error" not in r]
    eq = sum(r["equal"] for r in ok)
    print(f"functions {len(ok)}, byte-identical {eq}, differing {len(ok) - eq}, not in cg_clif's object "
          f"{len(rows) - len(ok)}; .text bytes stock {sum(r['stock'] for r in ok)}, "
          f"lean {sum(r['lean'] for r in ok)}")
    funcs, lines, only = Counter(), Counter(), Counter()
    for r in ok:
        c = r.get("causes", {})
        for k, v in c.items():
            funcs[k] += 1
            lines[k] += v
        if len(c) == 1:
            only[next(iter(c))] += 1
    print(f"{'cause':16} {'functions':>9} {'only cause':>10} {'insn lines':>10}")
    for k, v in funcs.most_common():
        print(f"{k:16} {v:9} {only[k]:10} {lines[k]:10}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json")
    ap.add_argument("--diffs")
    ap.add_argument("dirs", nargs="+")
    args = ap.parse_args()
    rows = compare(args.dirs, args.diffs)
    if args.json:
        Path(args.json).write_text(json.dumps(rows, indent=1) + "\n")
    summary(rows)


if __name__ == "__main__":
    main()
