#!/usr/bin/env python3
"""BaselineD2 (option D, scratch): release byte parity per crate, from stock-crate-parity.py's
first line in rel-<cl>/<crate>/parity-{fv,optfv}.txt (BaselineD1's m1) and relp-0.136.1 (the
prototype drop), plus notrap-dead.py counts of the dumps (unopt / opt CLIF).
  sum.py   -> markdown table on stdout
"""
import json, pathlib, re

B = pathlib.Path.home() / "clifv/tmp/BaselineD1"
B2 = pathlib.Path.home() / "clifv/tmp/BaselineD2"
CR = ["num-traits-0.2.19", "blake2-0.11.0", "sha3-0.12.0", "itoa-1.0.19", "semver-1.0.28",
      "ryu-1.0.23", "memchr-2.8.3", "serde_json-1.0.154", "crypto-bigint-0.7.11"]
COLS = [("unopt 0.135.0", B / "rel-0.135.0", "fv"), ("unopt 0.136.1", B / "rel-0.136.1", "fv"),
        ("unopt 0.136.1 + drop", B2 / "relp-0.136.1", "fv"),
        ("opt 0.135.0", B / "rel-0.135.0", "optfv"), ("opt 0.136.1", B / "rel-0.136.1", "optfv"),
        ("opt 0.136.1 + drop", B2 / "relp-0.136.1", "optfv")]


def parity(d, crate, p):
    f = d / crate / f"parity-{p}.txt"
    if not f.exists():
        return None
    m = re.match(r"functions (\d+), byte-identical (\d+)", f.read_text())
    return (int(m.group(2)), int(m.group(1))) if m else None


def dead(cl, crate, kind):
    f = B / f"rel-{cl}" / crate / f"notrap-{kind}.json"
    if not f.exists():
        return None
    rows = json.loads(f.read_text())
    return sum(1 for r in rows if r.get("direct") or r.get("chain")), len(rows)


tot = {c: [0, 0] for c, _, _ in COLS}
print("| crate | " + " | ".join(c for c, _, _ in COLS) + " | fns with unused notrap load: unopt / opt CLIF (0.136.1 dumps) |")
print("|---" * (len(COLS) + 2) + "|")
for crate in CR:
    cells = []
    for c, d, p in COLS:
        v = parity(d, crate, p)
        if v:
            tot[c][0] += v[0]; tot[c][1] += v[1]
            cells.append(f"{v[0]:,} / {v[1]:,} ({100 * v[0] / v[1]:.1f} %)")
        else:
            cells.append("n/a")
    du, do = dead("0.136.1", crate, "unopt"), dead("0.136.1", crate, "opt")
    dd = f"{du[0]:,} / {do[0]:,} (of {du[1]:,})" if du and do else "n/a"
    print(f"| {crate} | " + " | ".join(cells) + f" | {dd} |")
print("| **total** | " + " | ".join(f"{a:,} / {b:,} ({100 * a / b:.1f} %)" if b else "n/a" for a, b in tot.values()) + " | |")
