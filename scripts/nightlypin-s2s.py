#!/usr/bin/env python3
"""NightlyPin1 experiment (agent/NightlyPin1 only, not for main): per-function comparison of two
`cargo fv --keep-temps` runs of the same crate whose cg_clif differs only in its Cranelift version
(A = 0.135.0, B = 0.136.1). Functions are matched by symbol (the `_fv_<cgu>_` prefix of local
symbols removed). For every function Lean compiled in both runs it reports whether stock's bytes
changed (A vs B), whether Lean's did, and Lean == stock in each run; for stock-changed functions
it attributes the A→B difference with stock-crate-parity.py's cause heuristics.

usage: scripts/nightlypin-s2s.py KEEP_A KEEP_B [--diffs DIR] [--json OUT]
  KEEP_*: directories of CGU dirs holding cgclif.o and lean.o
"""
import argparse
from collections import Counter
import difflib
import importlib.util
import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("scp", here / "stock-crate-parity.py")
scp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scp)
ELF = scp.ELF


def norm(name):
    return re.sub(r"^_fv_[0-9a-f]{12}_", "", name)


def code(keep, obj):
    out = {}
    for f in sorted(Path(keep).glob(f"*/{obj}")):
        elf = ELF(f)
        for name, syms in elf.functions.items():
            if len(syms) != 1 or not syms[0]["size"]:
                continue
            s, b = elf.function(name)
            rel = [(r["offset"], r["type"], r["addend"]) for r in elf.function_relocations(s, {})]
            out.setdefault(norm(name), []).append((b, rel))
    # a name defined in several CGUs with different code is ambiguous: drop it
    return {k: v[0] for k, v in out.items() if all(x == v[0] for x in v)}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("a")
    ap.add_argument("b")
    ap.add_argument("--diffs")
    ap.add_argument("--json")
    args = ap.parse_args()
    sa, sb = code(args.a, "cgclif.o"), code(args.b, "cgclif.o")
    la, lb = code(args.a, "lean.o"), code(args.b, "lean.o")
    names = sorted(set(la) & set(lb) & set(sa) & set(sb))
    rows, cls, causes, only = [], Counter(), Counter(), Counter()
    for n in names:
        r = {"fn": n, "stock_same": sa[n] == sb[n], "lean_same": la[n] == lb[n],
             "lean_eq_a": la[n] == sa[n], "lean_eq_b": lb[n] == sb[n]}
        cls[(r["lean_eq_a"], r["lean_eq_b"])] += 1
        if not r["stock_same"]:
            a, b = scp.disasm(sa[n][0]), scp.disasm(sb[n][0])
            c = dict(scp.analyse(a, b)) or {"relocations": 1}
            r["causes"] = c
            causes.update(c.keys())
            if len(c) == 1:
                only.update(c.keys())
            if args.diffs:
                Path(args.diffs).mkdir(parents=True, exist_ok=True)
                (Path(args.diffs) / f"{n[:150]}.diff").write_text(
                    "\n".join(difflib.unified_diff(a, b, "stock-0.135.0", "stock-0.136.1", lineterm="", n=2)) + "\n")
        rows.append(r)
    if args.json:
        Path(args.json).write_text(json.dumps(rows, indent=1) + "\n")
    print(f"functions Lean-compiled in both runs (matched by symbol): {len(names)} "
          f"(A only {len(set(la) - set(lb))}, B only {len(set(lb) - set(la))})")
    print(f"stock bytes changed 0.135.0 -> 0.136.1: {sum(not r['stock_same'] for r in rows)}; "
          f"Lean bytes changed between the runs: {sum(not r['lean_same'] for r in rows)}")
    print(f"Lean == stock: with 0.135.0 {sum(r['lean_eq_a'] for r in rows)}, with 0.136.1 {sum(r['lean_eq_b'] for r in rows)}")
    print(f"  equal to both {cls[(True, True)]}, only to 0.135.0 {cls[(True, False)]}, "
          f"only to 0.136.1 {cls[(False, True)]}, to neither {cls[(False, False)]}")
    print("causes of the stock change (functions, of them as only cause):")
    for k, v in causes.most_common():
        print(f"  {k:16} {v:6} {only[k]:6}")


if __name__ == "__main__":
    main()
