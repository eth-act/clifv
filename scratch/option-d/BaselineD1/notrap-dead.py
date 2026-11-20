#!/usr/bin/env python3
"""BaselineD1 (option D, scratch): functions whose CLIF (the .unopt.clif Lean compiles) has a
`notrap` load whose result no instruction uses, i.e. what Cranelift 0.136.1 does not lower and
0.135.0 / our compiler do. Optionally joined with nightlypin-s2s.py's per-function JSON (did
stock's bytes change 0.135.0 -> 0.136.1?) to show whether any OTHER stock change exists.

  notrap-dead.py [--s2s S2S.json] [--json OUT] [--suffix .unopt.clif] DIR...
  DIR: kept temps (<cgu>/c.clif/*.clif) or dump dirs (*.clif files below it)

direct: the load's result has no use. chain: removing dead notrap loads and dead pure
instructions to a fixpoint removes at least one more notrap load (a dead load chain).
"""
import argparse, collections, json, re
from pathlib import Path

LOADS = {"load", "uload8", "sload8", "uload16", "sload16", "uload32", "sload32"}
# instructions with an effect besides their results (never removed when unused)
EFFECT = re.compile(r"^(store|istore\d+|stack_store|call|call_indirect|try_call|try_call_indirect|return|return_call"
                    r"|return_call_indirect|jump|brif|br_table|trap|trapz|trapnz|debugtrap|udiv|sdiv|urem|srem"
                    r"|fcvt_to_uint|fcvt_to_sint|uadd_overflow_trap|atomic_\w+|fence|set_pinned_reg|nop"
                    r"|dynamic_stack_store|stack_switch|sequence_point)$")
VAL = re.compile(r"\bv(\d+)\b")
INST = re.compile(r"^\s*((?:v\d+(?:, *v\d+)*) *= *)?([a-z_0-9]+)(\.[a-z0-9x]+)?\b(.*)$")


def norm(name):
    return re.sub(r"^_?_fv_[0-9a-f]{12}_", "", name)


def analyse(text):
    sym = None
    insts = []  # (defs, opcode, uses, flags-rest)
    alias = {}
    for ln in text.splitlines():
        if ln.startswith("; symbol "):
            sym = ln[len("; symbol "):].strip()
            continue
        s = re.sub(r"^@[0-9a-f]+\s+", "", ln.split(";")[0].strip())
        if not s or s.startswith(("function", "block", "}", "set ", "target", "ss", "sig", "fn", "gv", "jt", "const")):
            continue
        m = re.match(r"^v(\d+) -> v(\d+)$", s)
        if m:
            alias[int(m.group(1))] = int(m.group(2))
            continue
        m = INST.match(s)
        if not m:
            continue
        defs = [int(x) for x in VAL.findall(m.group(1) or "")]
        uses = [int(x) for x in VAL.findall(m.group(4))]
        insts.append((defs, m.group(2), uses, m.group(4)))

    def res(v):
        seen = set()
        while v in alias and v not in seen:
            seen.add(v)
            v = alias[v]
        return v

    insts = [(d, op, [res(u) for u in us], rest) for d, op, us, rest in insts]
    cnt = collections.Counter(u for _, _, us, _ in insts for u in us)
    notrap = [i for i, (d, op, _, rest) in enumerate(insts) if op in LOADS and re.search(r"\bnotrap\b", rest)]
    direct = [i for i in notrap if insts[i][0] and all(cnt[v] == 0 for v in insts[i][0])]
    # fixpoint: drop dead notrap loads and dead effect-free non-load instructions
    alive = [True] * len(insts)
    changed = True
    while changed:
        changed = False
        for i, (d, op, us, rest) in enumerate(insts):
            if not alive[i] or not d or any(cnt[v] for v in d):
                continue
            droppable = (op in LOADS and re.search(r"\bnotrap\b", rest)) or (op not in LOADS and not EFFECT.match(op))
            if droppable:
                alive[i] = False
                changed = True
                for u in us:
                    cnt[u] -= 1
    chain = [i for i in notrap if not alive[i]]
    return sym, len(notrap), len(direct), len(chain)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--s2s")
    ap.add_argument("--json")
    ap.add_argument("--suffix", default=".unopt.clif")
    ap.add_argument("dirs", nargs="+")
    a = ap.parse_args()
    rows = {}
    for d in a.dirs:
        for f in Path(d).rglob("*" + a.suffix):
            sym, n, dd, ch = analyse(f.read_text(errors="replace"))
            key = norm(sym or f.name[: -len(a.suffix)])
            r = rows.setdefault(key, {"fn": key, "notrap": n, "direct": dd, "chain": ch})
            r["direct"] = max(r["direct"], dd)
            r["chain"] = max(r["chain"], ch)
    fns = len(rows)
    withn = sum(r["notrap"] > 0 for r in rows.values())
    direct = sum(r["direct"] > 0 for r in rows.values())
    chain = sum(r["chain"] > 0 for r in rows.values())
    extra = sum(r["chain"] > r["direct"] for r in rows.values())
    print(f"functions {fns}: with a notrap load {withn}; with an unused notrap load {direct} "
          f"({sum(r['direct'] for r in rows.values())} loads); dead after the fixpoint {chain} "
          f"({sum(r['chain'] for r in rows.values())} loads; {extra} functions with more than the direct ones)")
    if a.s2s:
        s2s = {norm(r["fn"]): r for r in json.loads(Path(a.s2s).read_text())}
        c = collections.Counter()
        others = []
        for k, r in s2s.items():
            x = rows.get(k)
            if x is None:
                c["no-clif"] += 1
                continue
            dead = x["chain"] > 0
            c[("stock-changed" if not r["stock_same"] else "stock-same", "dead-load" if dead else "no-dead-load")] += 1
            if not r["stock_same"] and not dead:
                others.append(k)
            if dead and r["lean_eq_a"]:
                c["dead-load & lean==stock0.135"] += 1
                c["... & lean==stock0.136.1"] += r["lean_eq_b"]
        for k, v in sorted(c.items(), key=str):
            print(f"  s2s join {k}: {v}")
        for k in others[:30]:
            print(f"  stock changed without a dead notrap load: {k} causes={s2s[k].get('causes')}")
    if a.json:
        Path(a.json).write_text(json.dumps(sorted(rows.values(), key=lambda r: r["fn"])) + "\n")


if __name__ == "__main__":
    main()
