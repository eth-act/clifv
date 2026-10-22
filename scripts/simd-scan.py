#!/usr/bin/env python3
"""Vector-typed CLIF in cg_clif dumps (S12, #36; docs/plans/simd.md section 1).

usage: scripts/simd-scan.py DIR... [--list]

Scans every `*.unopt.clif` below the given directories (cg_clif's per-function dumps, e.g. a
`cargo fv` target directory or `scripts/rust-clif/core.sh`'s `clif/{core,alloc}`) and reports the
functions with a vector type (`i8x16`, `i64x2`, `f32x4`, …; CLIF spelling `<lane>x<lanes>`):
the number of such functions, and per construct the number of functions using it. A construct is
the opcode of an instruction whose result or operand type is a vector (`load.i64x2`, `store`
of a vector value, `bitcast`, …), `param` (a vector block or function parameter), or `sig`
(a vector in a signature declaration). Dumps of the same symbol (cargo fv keeps `c.clif/` and
`split/` copies) count once. --list prints each function (symbol, path, constructs).
"""
import argparse, collections, os, re, sys

VTY = re.compile(r"\b[if](?:8|16|32|64)x\d+\b")
DEF = re.compile(r"^\s*(?:@[0-9a-f]+\s+)?(v\d+(?:\s*,\s*v\d+)*)\s*=\s*([a-z_0-9]+)(?:\.([a-z0-9]+))?\s*(.*)$")
STMT = re.compile(r"^\s*(?:@[0-9a-f]+\s+)?([a-z_0-9]+)(?:\.([a-z0-9]+))?\s+(.*)$")
BLOCK = re.compile(r"^\s*block\d+\((.*)\):")
FUNC = re.compile(r"^function\s+\S+\((.*)\)(?:\s*->\s*(.*?))?\s+\w+\s*\{")
DECL = re.compile(r"^\s*(sig\d+|fn\d+)\s*=\s*(.*)$")
VAL = re.compile(r"\bv\d+\b")


def scan(path):
    """Constructs of one dump that involve a vector type (empty: none)."""
    found = set()
    vty = set()  # values of vector type
    with open(path, errors="replace") as fh:
        lines = [l for l in fh if not l.lstrip().startswith(";")]
    for line in lines:
        m = FUNC.match(line)
        if m:
            if VTY.search(m.group(1) or "") or VTY.search(m.group(2) or ""):
                found.add("param")
            for p in re.finditer(r"(v\d+)\s*:\s*([a-z0-9]+)", m.group(1) or ""):
                if VTY.fullmatch(p.group(2)):
                    vty.add(p.group(1))
            continue
        m = BLOCK.match(line)
        if m:
            for p in re.finditer(r"(v\d+)\s*:\s*([a-z0-9]+)", m.group(1)):
                if VTY.fullmatch(p.group(2)):
                    vty.add(p.group(1))
                    found.add("param")
            continue
        m = DECL.match(line)
        if m:
            if m.group(1).startswith("sig") and VTY.search(m.group(2)):
                found.add("sig")
            continue
        m = DEF.match(line)
        if m:
            res, op, ty, rest = m.groups()
            uses = VAL.findall(rest)
            if (ty and VTY.fullmatch(ty)) or VTY.search(rest):
                for v in res.split(","):
                    vty.add(v.strip())
                found.add(f"{op}.{ty}" if ty else op)
            elif any(u in vty for u in uses):
                found.add(op)
            continue
        m = STMT.match(line)
        if m:
            op, ty, rest = m.groups()
            if (ty and VTY.fullmatch(ty)) or any(u in vty for u in VAL.findall(rest)):
                found.add(f"{op}.{ty}" if ty else op)
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dirs", nargs="+")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    seen = {}
    total = 0
    for d in a.dirs:
        for root, _, files in os.walk(d):
            for f in files:
                if not f.endswith(".unopt.clif"):
                    continue
                sym = f[: -len(".unopt.clif")]
                if sym in seen:
                    continue
                total += 1
                p = os.path.join(root, f)
                with open(p, errors="replace") as fh:
                    text = fh.read()
                seen[sym] = (p, scan(p) if VTY.search(text) else set())
    hits = {s: v for s, v in seen.items() if v[1]}
    print(f"dumps (distinct symbols): {total}")
    print(f"functions with vector-typed CLIF: {len(hits)}")
    per = collections.Counter(c for _, cs in hits.values() for c in cs)
    for c, n in sorted(per.items(), key=lambda x: (-x[1], x[0])):
        print(f"  {c:24} {n}")
    if a.list:
        for s, (p, cs) in sorted(hits.items()):
            print(f"{s}\t{p}\t{' '.join(sorted(cs))}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
