#!/usr/bin/env python3
"""BaselineD3 (option D, scratch): same-worktree join (wt BaselineD1, Cranelift 0.136.1) of the
prototype's s2sref (A = drop off, B = drop on) with notrap-dead.py on the same keep dir
(BaselineD3/notrapP-LINE.json): does the drop change exactly the functions with an unused notrap
load, and where does it leave Lean != stock.   join2.py LINE   (cwd ~/clifv/tmp/BaselineD2)"""
import collections, json, re, sys

line = sys.argv[1]
S = json.load(open(f"proto5on/s2sref-{line}-0.136.1.json"))
N = {r["fn"]: r for r in json.load(open(f"../BaselineD3/notrapP-{line}.json"))}
c = collections.Counter()
ex = collections.defaultdict(list)
for r in S:
    t = N.get(re.sub(r"^_?_fv_[0-9a-f]{12}_", "", r["fn"]))
    dead = "n/a" if t is None else ("dead" if (t["direct"] or t["chain"]) else "no-dead")
    dropped = not r["lean_same"]
    key = f"{dead:7} drop-changed={dropped!s:5} off==stock={r['lean_eq_a']!s:5} on==stock={r['lean_eq_b']!s:5}"
    c[key] += 1
    ex[key].append(r["fn"])
for k, v in sorted(c.items()):
    print(f"{v:7}  {k}  e.g. {ex[k][0]}")
