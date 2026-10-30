#!/usr/bin/env python3
"""Find imports on the critical path that serialize the build for a few constants.

usage: scripts/shake/chain.py FACTS.jsonl [--cap 300] [--top 40] [--profile TSV]...

Uses the import graph and recorded module times (as scripts/shake/measure.py) and, for the
modules of the capped critical chain, their constant-level references (scripts/shake/Refs.lean,
run here). For every chain edge A -> B (A imports B) it reports what A uses of B: the constants
of B that A mentions, their closure inside B (what would have to move to a lower module so that
A need not import B), the modules that closure needs, and the depth A would have if it imported
that lower module instead of B (the other modules A needs from B's closure imported directly).
"""
import argparse, json, pathlib, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import measure  # noqa: E402

ROOT = measure.ROOT


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("facts")
    ap.add_argument("--cap", type=float, default=300)
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument("--profile", action="append", default=[])
    ap.add_argument("--refs", help="reuse a Refs.lean output")
    a = ap.parse_args()
    facts = {}
    for line in open(a.facts):
        d = json.loads(line)
        if "m" in d:
            facts[d["m"]] = d
    g = {m: [x for x in f["imports"] if x in facts] for m, f in facts.items()}
    secs = measure.load_secs(a.profile)
    w = {m: min(secs.get(m, 60.0), a.cap) for m in g}
    order = measure.topo(g, g)
    depth, prev = {}, {}
    for m in order:
        best = max(((depth[d], d) for d in g[m]), default=(0.0, None))
        depth[m], prev[m] = best[0] + w[m], best[1]
    end = max(depth, key=depth.get)
    chain = []
    x = end
    while x:
        chain.append(x)
        x = prev[x]
    chain.reverse()
    print(f"capped critical chain: {depth[end] / 3600:.2f} h, {len(chain)} modules")
    refs_path = a.refs
    if not refs_path:
        refs_path = "/tmp/shake-refs.jsonl"
        pathlib.Path("/tmp/shake-chain.txt").write_text("\n".join(chain) + "\n")
        subprocess.run(["lake", "env", "lean", "--run", "scripts/shake/Refs.lean", refs_path,
                        "/tmp/shake-chain.txt"], cwd=ROOT, check=True)
    consts = {}   # name -> record
    by_mod = {}
    for line in open(refs_path):
        d = json.loads(line)
        consts[d["c"]] = d
        by_mod.setdefault(d["m"], []).append(d["c"])
    T = {}
    for m in order:
        t = set()
        for y in g[m]:
            t |= {y} | T[y]
        T[m] = t
    rows = []
    for A, B in zip(chain[1:], chain[:-1]):
        if A not in by_mod or B not in by_mod:
            continue
        used = {r[0] for c in by_mod[A] for r in consts[c]["refs"] if r[1] == B}
        nonconst = B in facts[A]["extra"] or B in facts[A]["indirect"]
        # closure of `used` inside B
        L, st = set(used), list(used)
        while st:
            c = st.pop()
            for r, rm in consts.get(c, {}).get("refs", []):
                if rm == B and r not in L:
                    L.add(r)
                    st.append(r)
        D = {rm for c in L for _, rm in consts[c]["refs"] if rm != B}
        others = [y for y in g[A] if y != B]
        via = set()
        for y in others:
            via |= {y} | T[y]
        # what A needs from B's closure that its other imports do not provide
        need_through_B = {n for n in facts[A]["needs"] if n in T[B] and n not in via}
        dB0 = w[B] * len(L) / max(1, len(by_mod[B])) + max((depth[x] for x in D if x in depth), default=0)
        newA = w[A] + max([depth[y] for y in others] + [depth[x] for x in need_through_B] + [dB0])
        rows.append((depth[A] - newA, A, B, len(used), len(L), len(by_mod[B]),
                     sum(1 for c in L if consts[c]["priv"]), nonconst, sorted(used)[:6]))
    rows.sort(reverse=True)
    print("gain_s  A <- B  used/closure/|B|  private  non-constant-use  used constants")
    for r in rows[:a.top]:
        print(f"{r[0]:7.0f} {r[1]} <- {r[2]}  {r[3]}/{r[4]}/{r[5]}  priv={r[6]}  extra={r[7]}  {r[8]}")


if __name__ == "__main__":
    main()
