#!/usr/bin/env python3
"""Split a Lake build into waves of parallel CI shards (.github/workflows/full-gate.yml).

usage: scripts/ci-build-plan.py [options] TARGET...

TARGET as in scripts/lake-serial-build.py (a library name, a module, or a prefix ending in `.`).
With --base SHA (the commit whose complete build the CI cache holds), only modules whose source
differs from SHA, and their importers, are planned: Lake restores every other module from the
cache. Without --base, or when lakefile.toml / lean-toolchain / lake-manifest.json differ, all of
them are planned.

Waves run one after another; the shards of a wave run in parallel on separate runners. A module
belongs to the wave in which its earliest possible start (longest recorded-seconds import path
within the planned set) falls. A shard of a wave builds some of the wave's sinks (modules no other
module of the wave imports) with their imports from the same wave, so shards of one wave never
wait for each other (an import shared by several shards is built in each; where Lean's output
differs between those builds, scripts/lake-unstage.py picks one). Earlier waves' modules
come from the earlier waves' cache artifacts. Several splits are simulated with the recorded
per-module peaks and seconds (scripts/lake-module-peaks.tsv) and the scheduler limits CI uses
(lake-serial-build.py --budget/--heavy/--max-jobs), and the fastest is written.

Output (--out): JSON {"base", "all", "planned", "estimate_s", "waves": [[{"modules": [...],
"estimate_s"}, ...], ...]} with exactly --waves entries (later ones may be empty). With
--github-output, also appends `waveN=[0,1,...]` (shard indices for a job matrix), `planned=N` and
`estimate=H.Hh` to $GITHUB_OUTPUT.
"""
import argparse, collections, heapq, importlib.util, json, os, pathlib, subprocess, sys, tomllib

GiB = 1024 ** 3
HERE = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("lake_serial_build", HERE / "lake-serial-build.py")
lsb = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lsb)

GLOBAL_INPUTS = {"lakefile.toml", "lean-toolchain", "lake-manifest.json"}


# lean_exe keys that affect only the executable's link, not how any module is compiled
EXE_LINK_KEYS = {"name", "root", "exeName", "supportInterpreter", "moreLinkArgs"}


def lakefile_modules_same(root, base):
    """True if lakefile.toml differs from `base` only in lean_exe entries that set no compile
    options: adding an executable (most lakefile edits) leaves every module's build unchanged,
    and its root module is planned like any other changed or added file."""
    old = subprocess.run(["git", "show", f"{base}:lakefile.toml"], cwd=root,
                         capture_output=True, text=True)
    if old.returncode != 0:
        return False
    try:
        a, b = tomllib.loads(old.stdout), tomllib.loads((root / "lakefile.toml").read_text())
    except tomllib.TOMLDecodeError:
        return False
    exes = a.pop("lean_exe", []) + b.pop("lean_exe", [])
    if any(set(e) - EXE_LINK_KEYS for e in exes):
        return False
    if a == b:
        print(f"lakefile.toml changed since {base} only in lean_exe entries: planning changed "
              f"modules only", file=sys.stderr)
        return True
    return False


def changed_modules(root, base, libs, mods):
    """Modules whose source differs between `base` and HEAD, or None if everything is stale."""
    r = subprocess.run(["git", "diff", "--name-only", base, "HEAD", "--"], cwd=root,
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"git diff {base} failed ({r.stderr.strip()}): planning everything", file=sys.stderr)
        return None
    by_path = {p.resolve(): m for m, p in mods.items()}
    out = set()
    for f in r.stdout.split():
        if f == "lakefile.toml" and lakefile_modules_same(root, base):
            continue
        if f in GLOBAL_INPUTS:
            print(f"{f} changed since {base}: planning everything", file=sys.stderr)
            return None
        m = by_path.get((root / f).resolve())
        if m:
            out.add(m)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("targets", nargs="+")
    ap.add_argument("--root", default=".")
    ap.add_argument("--base", help="commit whose build the cache holds (default: none, plan all)")
    ap.add_argument("--shards", type=int, default=16, help="max shards per wave")
    ap.add_argument("--waves", type=int, default=3, help="number of wave jobs in the workflow")
    ap.add_argument("--wave-overhead", type=float, default=420,
                    help="seconds a wave costs besides building (runner start, restore, upload)")
    ap.add_argument("--budget", default="15G")
    ap.add_argument("--heavy", default="12G")
    ap.add_argument("--max-jobs", type=int, default=3)
    ap.add_argument("--margin", type=float, default=1.0)
    ap.add_argument("--min-cap", default="3G")
    ap.add_argument("--default-cap", default="6G")
    ap.add_argument("--default-secs", type=float, default=60)
    ap.add_argument("--time-scale", type=float, default=1.0,
                    help="runner seconds per recorded second (recorded on the agents' machine)")
    ap.add_argument("--prefix-scale", action="append", default=[], metavar="PREFIX=F",
                    help="modules starting with PREFIX run F times slower than --time-scale says "
                         "(repeatable; longest match wins)")
    ap.add_argument("--ram", default="0",
                    help="runner RAM; a module whose recorded peak exceeds it pages to swap, and "
                         "its estimate grows by --swap-penalty per GiB above (0: no penalty)")
    ap.add_argument("--swap-penalty", type=float, default=1.8,
                    help="extra runner seconds per recorded second and GiB above --ram (GitHub "
                         "runner, 16 GB + 24 GB swap: StockCmpWithFlags, 23.6 GB peak, ran "
                         "27-45x longer, median 31.6x, at time scale 2)")
    ap.add_argument("--profile", action="append")
    ap.add_argument("--out", default="ci-plan.json")
    ap.add_argument("--github-output", action="store_true")
    a = ap.parse_args()

    root = pathlib.Path(a.root).resolve()
    libs, mods, imports = lsb.load_modules(root)
    prof = lsb.load_profile(a.profile or [root / "scripts/lake-module-peaks.tsv"])
    budget, heavy = lsb.size(a.budget), lsb.size(a.heavy)
    min_cap, default_cap = lsb.size(a.min_cap), lsb.size(a.default_cap)

    roots = set()
    for t in a.targets:
        if t in libs:
            roots |= {m for m in mods if m == t or m.startswith(t + ".")}
        elif t.endswith("."):
            roots |= {m for m in mods if m.startswith(t)}
        elif t in mods:
            roots.add(t)
        else:
            sys.exit(f"unknown target {t}")
    want, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m not in want:
            want.add(m)
            stack.extend(imports[m])

    changed = changed_modules(root, a.base, libs, mods) if a.base else None
    if changed is None:
        planned = set(want)
    else:
        rdeps = collections.defaultdict(list)
        for m in want:
            for d in imports[m]:
                rdeps[d].append(m)
        planned, stack = set(), [m for m in changed if m in want]
        while stack:
            m = stack.pop()
            if m not in planned:
                planned.add(m)
                stack.extend(rdeps[m])

    ram = lsb.size(a.ram)
    peak = {m: prof[m][0] if m in prof else 0 for m in planned}
    prefix_scale = sorted(((p, float(x)) for p, x in (s.split("=", 1) for s in a.prefix_scale)),
                          key=lambda px: -len(px[0]))

    def scale(m):
        return a.time_scale * next((f for p, f in prefix_scale if m.startswith(p)), 1.0)

    secs = {m: scale(m) * (prof[m][1] if m in prof else a.default_secs)
               * (1 + a.swap_penalty * max(0, peak[m] - ram) / GiB if ram else 1) for m in planned}

    def cap(m):
        if m not in prof:
            return default_cap
        c = prof[m][0] * a.margin + GiB // 2
        return max(min_cap, int(-(-c // GiB)) * GiB)

    caps = {m: cap(m) for m in planned}
    deps = {m: [d for d in imports[m] if d in planned] for m in planned}
    rdeps = {m: [] for m in planned}
    for m in planned:
        for d in deps[m]:
            rdeps[d].append(m)
    order = []  # topological (imports first)
    indeg = {m: len(deps[m]) for m in planned}
    q = sorted(m for m in planned if indeg[m] == 0)
    while q:
        m = q.pop()
        order.append(m)
        for r in rdeps[m]:
            indeg[r] -= 1
            if indeg[r] == 0:
                q.append(r)
    est = {}
    for m in order:
        est[m] = max((est[d] + secs[d] for d in deps[m]), default=0.0)
    tail = {}
    for m in reversed(order):
        tail[m] = secs[m] + max((tail[r] for r in rdeps[m]), default=0.0)
    cp = max((est[m] + secs[m] for m in planned), default=0.0)
    pos = {m: i for i, m in enumerate(order)}

    def work(ms):
        # a module with more than half the budget runs alone, lighter ones about two at a time
        return sum(secs[x] / (1 if caps[x] > budget / 2 else 2) for x in ms)

    def is_heavy(m):
        return peak[m] > heavy or caps[m] > budget

    def simulate(todo):
        """Wall seconds of lake-serial-build.py on `todo` (imports outside it are built)."""
        indeg = {m: sum(1 for d in deps[m] if d in todo) for m in todo}
        ready = [(-tail[m], m) for m in todo if indeg[m] == 0]
        heapq.heapify(ready)
        t, run, used = 0.0, [], 0
        while ready or run:
            solo = any(is_heavy(x) for _, x in run)
            skipped = []
            while ready and not solo and len(run) < a.max_jobs:
                item = heapq.heappop(ready)
                m = item[1]
                if is_heavy(m):
                    if run:
                        skipped.append(item)
                        break
                    heapq.heappush(run, (t + secs[m], m)); used += caps[m]; solo = True
                    break
                if used + caps[m] > budget:
                    skipped.append(item)
                    continue
                heapq.heappush(run, (t + secs[m], m)); used += caps[m]
            for item in skipped:
                heapq.heappush(ready, item)
            e, m = heapq.heappop(run)
            t, used = e, used - caps[m]
            for r in rdeps[m]:
                if r in indeg:
                    indeg[r] -= 1
                    if indeg[r] == 0:
                        heapq.heappush(ready, (-tail[r], r))
        return t

    def split(cuts):
        waves = []
        for i, c0 in enumerate(cuts):
            c1 = cuts[i + 1] if i + 1 < len(cuts) else float("inf")
            wm = {m for m in planned if c0 <= est[m] < c1}
            if not wm:
                continue
            sinks = [m for m in wm if not any(r in wm for r in rdeps[m])]
            clos, path = {}, {}
            for s in sinks:
                c, st = set(), [s]
                while st:
                    x = st.pop()
                    if x not in c:
                        c.add(x)
                        st.extend(d for d in deps[x] if d in wm)
                clos[s] = c
                longest = {}
                for x in sorted(c, key=pos.get):
                    longest[x] = secs[x] + max((longest[d] for d in deps[x] if d in c), default=0)
                path[s] = longest[s]
            sinks.sort(key=lambda s: (-sum(secs[x] for x in clos[s]), s))
            # greedy, biggest sinks first: join the shard whose estimate (longest import path,
            # or work spread over the slots a runner's memory allows) grows least, as long as
            # that does not raise the wave's longest shard; otherwise open a new shard
            shards = []  # [modules, work, longest path]
            for s in sinks:
                best = None
                for i, (ms, w, lp) in enumerate(shards):
                    nw = w + work(clos[s] - ms)
                    cost = max(nw, lp, path[s])
                    if best is None or cost < best[0]:
                        best = (cost, i, nw)
                longest = max((max(w, lp) for _, w, lp in shards), default=0.0)
                if best is None or (best[0] > longest and len(shards) < a.shards):
                    shards.append([set(clos[s]), work(clos[s]), path[s]])
                else:
                    ms, _, lp = shards[best[1]]
                    ms |= clos[s]
                    shards[best[1]] = [ms, best[2], max(lp, path[s])]
            waves.append([(ms, simulate(ms)) for ms, _, _ in shards])
        total = sum(max(t for _, t in w) + a.wave_overhead for w in waves)
        return total, waves

    best = None
    if planned:
        cands = [[0.0]]
        fr = [0.15, 0.25, 0.35, 0.45, 0.55]
        if a.waves >= 2:
            cands += [[0.0, f * cp] for f in fr]
        if a.waves >= 3:
            cands += [[0.0, f * cp, g * cp] for f in fr for g in fr + [0.65, 0.75] if g > f]
        for cuts in cands:
            total, waves = split(cuts)
            if len(waves) <= a.waves and (best is None or total < best[0]):
                best = (total, waves, cuts)
    total, waves, cuts = best if best else (0.0, [], [])
    plan = {
        "base": a.base, "all": changed is None, "planned": len(planned),
        "estimate_s": round(total), "critical_path_s": round(cp),
        "serial_s": round(sum(secs.values())),
        "waves": [[{"modules": sorted(ms), "estimate_s": round(t)} for ms, t in w] for w in waves]
                 + [[] for _ in range(a.waves - len(waves))],
    }
    pathlib.Path(a.out).write_text(json.dumps(plan, indent=1) + "\n")
    print(f"{len(planned)} of {len(want)} modules planned "
          f"({'all' if changed is None else f'{len(changed)} changed since {a.base}'}); "
          f"critical path {cp / 3600:.2f} h, serial {sum(secs.values()) / 3600:.2f} h (recorded)")
    for i, w in enumerate(plan["waves"]):
        if w:
            print(f"wave {i + 1}: {len(w)} shards, {sum(len(s['modules']) for s in w)} module builds, "
                  f"longest shard {max(s['estimate_s'] for s in w) / 3600:.2f} h")
    print(f"estimate {total / 3600:.2f} h (cuts at {[round(c) for c in cuts]} s)")
    if a.github_output:
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            for i, w in enumerate(plan["waves"]):
                f.write(f"wave{i + 1}={json.dumps(list(range(len(w))))}\n")
            f.write(f"planned={len(planned)}\nestimate={total / 3600:.1f}h\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
