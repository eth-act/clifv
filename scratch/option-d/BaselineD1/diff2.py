#!/usr/bin/env python3
"""MidendNorm1: OLD -> NEW verdicts (dirs of <crate>.tsv): accepted counts, newly accepted pairs
(distinct pairs) with their counterfactual status from ReleaseScope1 (parity-optfv.json:
Lean-compiled from g, verified; equal = byte-identical to stock), lost pairs. Writes newly pairs
to ARGV[3]."""
import collections, json, pathlib, re, sys
old, new = map(pathlib.Path, sys.argv[1:3])
rd = pathlib.Path.home() / "clifv/tmp/ReleaseScope1/results"
def key(line):
    p = line.split("\t")
    return (re.sub(r".*/dumps/", "", p[0]), p[1]), p
c = collections.Counter(); newly = []; lost = []
for t in sorted(new.glob("*.tsv")):
    crate = t.stem
    o = dict(key(l) for l in (old / t.name).read_text().splitlines() if l)
    n = dict(key(l) for l in t.read_text().splitlines() if l)
    opt = collections.defaultdict(list)
    pj = rd / crate / "parity-optfv.json"
    for f in json.loads(pj.read_text()):
        opt[re.sub(r"^__fv_[0-9a-f]+_", "", f["fn"])].append(f["equal"])
    for k, p in n.items():
        c["pairs"] += 1
        acc = p[2] == "accept"; c["accepted"] += acc
        if acc and p[7] != "ok": c["recheck not ok"] += 1
        q = o[k]; oacc = q[2] == "accept"; c["old accepted"] += oacc
        if acc and not oacc:
            c["newly"] += 1
            e = opt.get(k[1])
            if e: c["newly: verified from g"] += 1; c["newly: identical from g"] += all(e)
            else: c["newly: not in optfv"] += 1
            newly.append((crate, k, q[3], p[4], p[5]))
        if oacc and not acc:
            c["lost"] += 1; lost.append((crate, k, p[3]))
        if acc:
            e = opt.get(k[1])
            if e: c["accepted: verified from g"] += 1; c["accepted: identical from g"] += all(e)
            else: c["accepted: not in optfv"] += 1
for k, v in c.items(): print(f"{k}\t{v}")
for l in lost[:20]: print("LOST", l)
if len(sys.argv) > 3:
    pathlib.Path(sys.argv[3]).write_text("".join(f"{cr}\t{k[0]}\t{k[1]}\t{r}\t{fi}\t{gi}\n" for cr, k, r, fi, gi in newly))
