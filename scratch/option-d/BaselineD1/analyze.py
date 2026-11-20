#!/usr/bin/env python3
"""#1119 stage 1 (MidendVal1): aggregate midval-check verdicts per crate and join them with
ReleaseScope1's opt-input counterfactual (byte parity of each function compiled from its
.opt.clif, `parity-optfv.json`; a function listed there was compiled by Lean and verified) and
its unopt-input run (`parity-fv.json`, today's bytes).

usage: analyze.py VERDICTS_DIR RESULTS_DIR
  VERDICTS_DIR/<crate>.tsv  midval-check output (dir, stem, verdict, reason, insts f, insts g, us)
  RESULTS_DIR/<crate>/parity-{fv,optfv}.json  (ReleaseScope1)
"""
import collections, json, pathlib, re, sys

vd, rd = map(pathlib.Path, sys.argv[1:3])
tot = collections.Counter()
reasons = collections.Counter()
reasons_fine = collections.Counter()
patterns = collections.Counter()
rows = []
times = []
for tsv in sorted(vd.glob("*.tsv")):
    crate = tsv.stem
    c = collections.Counter()
    verdict = {}
    for line in tsv.read_text().splitlines():
        p = line.split("\t")
        if len(p) < 7:
            continue
        _, stem, v, reason, fi, gi, us = p[:7]
        c["pairs"] += 1
        c[v] += 1
        times.append(int(us))
        c["us"] += int(us)
        if v == "reject":
            cls = reason.split(" ")[0]
            if cls.startswith("wf:"):
                cls = "wf:" + ("bitcast/typing" if "ill-typed" in reason else "call_indirect/result types" if "ill-formed instruction" in reason else reason.split(":")[1].split(" ")[0])
            reasons[cls] += 1
            fine = re.sub(r" block\d+", "", reason)
            fine = re.sub(r"defining \[[0-9, ]*\]", "defining […]", fine)
            reasons_fine[fine] += 1
            if cls == "rewrite:operand":
                parts = re.sub(r" block\d+", "", reason).split(" ")
                patterns[" ".join(parts[2:]) or "?"] += 1
        verdict[stem] = verdict.get(stem, True) and v == "accept"
    # join with the counterfactual's per-function parity
    def load(name):
        out = collections.defaultdict(list)
        p = rd / crate / name
        if p.exists():
            for f in json.loads(p.read_text()):
                out[re.sub(r"^__fv_[0-9a-f]+_", "", f["fn"])].append(f)
        return out
    fv, opt = load("parity-fv.json"), load("parity-optfv.json")
    for sym, recs in opt.items():
        v = verdict.get(sym)
        if v is None:
            c["opt-records-unmatched"] += len(recs)
            continue
        for r in recs:
            key = "acc" if v else "rej"
            c[f"{key}-verified-from-g"] += 1
            c[f"{key}-identical-from-g"] += r["equal"]
    for sym, recs in fv.items():
        v = verdict.get(sym)
        if v is None:
            c["fv-records-unmatched"] += len(recs)
            continue
        for r in recs:
            key = "acc" if v else "rej"
            c[f"{key}-verified-from-f"] += 1
            c[f"{key}-identical-from-f"] += r["equal"]
    rows.append((crate, c))
    tot.update(c)

def pct(a, b):
    return f"{a:,} / {b:,} ({100 * a / b:.1f} %)" if b else "-"

print("| crate | pairs | accepted | check time total (s) | mean (ms) | accepted: verified from g | accepted: identical to stock from g | accepted: identical today (from f) | rejected: identical today |")
print("|---|---|---|---|---|---|---|---|---|")
for crate, c in rows + [("**total**", tot)]:
    print(f"| {crate} | {c['pairs']:,} | {pct(c['accept'], c['pairs'])} | {c['us'] / 1e6:.1f} | {c['us'] / max(c['pairs'], 1) / 1e3:.2f} | "
          f"{c['acc-verified-from-g']:,} | {pct(c['acc-identical-from-g'], c['acc-verified-from-g'])} | "
          f"{pct(c['acc-identical-from-f'], c['acc-verified-from-f'])} | {pct(c['rej-identical-from-f'], c['rej-verified-from-f'])} |")
print()
print("unmatched parity records (opt, fv):", tot["opt-records-unmatched"], tot["fv-records-unmatched"])
times.sort()
if times:
    q = lambda f: times[min(len(times) - 1, int(f * len(times)))]
    print(f"check time per pair (us, ConstPhi.run + check, decode excluded): median {q(0.5)}, p90 {q(0.9)}, p99 {q(0.99)}, max {times[-1]}")
print()
print("rejections by class:")
for k, v in reasons.most_common():
    print(f"  {v:7,}  ({100 * v / tot['pairs']:.1f} %)  {k}")
print()
print("rejections, detail (top 40):")
for k, v in reasons_fine.most_common(40):
    print(f"  {v:7,}  {k}")
print()
print("rewrite:operand: first differing term heads f→g (top 40):")
for k, v in patterns.most_common(40):
    print(f"  {v:7,}  {k}")
acc_g_eq = tot["acc-identical-from-g"]
rej_f_eq = tot["rej-identical-from-f"]
print()
print(f"projected: accepted functions compiled from g ({tot['acc-verified-from-g']:,} verified, {acc_g_eq:,} identical), "
      f"rejected from f ({tot['rej-verified-from-f']:,} verified, {rej_f_eq:,} identical): "
      f"{pct(acc_g_eq + rej_f_eq, tot['acc-verified-from-g'] + tot['rej-verified-from-f'])} identical")
