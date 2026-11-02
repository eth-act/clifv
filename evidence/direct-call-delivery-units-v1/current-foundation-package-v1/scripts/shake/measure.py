#!/usr/bin/env python3
"""Graph-model build costs of the import graph of FV, FVTest and Corpus.

usage: scripts/shake/measure.py [--rev REV] [--days 14] [--history REF] [--closure MODULE]...

Reads the import lines at REV (default: the working tree) and reports:
* rebuilds per commit ("method C"): for every first-parent commit of REF (default origin/main) in
  the last --days days, the modules a contributor at that commit rebuilds: each modified module
  and every module that imports it (transitively) in the graph at REV; an added module counts only
  itself; deleted modules count nothing. Reported as total / mean / median modules, and as total
  recorded seconds (scripts/lake-module-peaks.tsv, then .lake/lake-module-peaks.tsv; 60 s for
  modules without a record);
* the critical path (longest chain of recorded seconds) of the whole graph and of each --closure
  module's import closure, also with every module capped at 300 s;
* with --chain, the capped critical chain module by module;
* the number of internal import edges and of (module, transitive import) pairs.
"""
import argparse, pathlib, re, statistics, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LIBS = {"FV": "FV", "FVTest": "FVTest", "Corpus": "corpus/dsl/Corpus"}


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def module_of(path):
    for head, d in LIBS.items():
        if path.startswith(d + "/") and path.endswith(".lean"):
            return ".".join([head] + path[len(d) + 1:-5].split("/"))
    return None


def load_graph(rev):
    import importlib.util
    spec = importlib.util.spec_from_file_location("shake", pathlib.Path(__file__).parent / "shake.py")
    shake = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(shake)
    if rev:
        files = [f for f in git("ls-tree", "-r", "--name-only", rev).split() if module_of(f)]
        texts = {f: git("show", f"{rev}:{f}") for f in files}
    else:
        files = [str(p.relative_to(ROOT)) for d in LIBS.values() for p in (ROOT / d).rglob("*.lean")]
        texts = {f: (ROOT / f).read_text() for f in files}
    g = {}
    for f, t in texts.items():
        g[module_of(f)] = [x for _, x, _ in shake.parse_header(t) if x.split(".")[0] in LIBS]
    return g


def load_secs(extra=()):
    secs = {}
    for p in [ROOT / "scripts/lake-module-peaks.tsv", ROOT / ".lake/lake-module-peaks.tsv",
              *map(pathlib.Path, extra)]:
        if p.exists():
            for line in p.read_text().splitlines():
                f = line.split("\t")
                if len(f) >= 3 and not line.startswith("#"):
                    try:
                        secs[f[0]] = float(f[2])
                    except ValueError:
                        pass
    return secs


def crit(g, secs, mods, cap=None):
    memo = {}
    order = topo(g, mods)
    for m in order:
        w = secs.get(m, 60.0)
        if cap:
            w = min(w, cap)
        best = max(((memo[d][0], d) for d in g[m] if d in memo), default=(0.0, None))
        memo[m] = (best[0] + w, best[1])
    end = max(memo, key=lambda m: memo[m][0])
    chain, x = [], end
    while x:
        chain.append(x)
        x = memo[x][1]
    return memo[end][0], chain[::-1]


def topo(g, mods):
    out, seen = [], set()
    for m in sorted(mods):
        stack = [(m, iter(g.get(m, ())))]
        if m in seen:
            continue
        seen.add(m)
        while stack:
            x, it = stack[-1]
            for y in it:
                if y in g and y not in seen:
                    seen.add(y)
                    stack.append((y, iter(g[y])))
                    break
            else:
                out.append(x)
                stack.pop()
    return out


def closure(g, m):
    seen, st = {m}, [m]
    while st:
        for y in g.get(st.pop(), ()):
            if y in g and y not in seen:
                seen.add(y)
                st.append(y)
    return seen


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rev")
    ap.add_argument("--days", type=int, default=14)
    ap.add_argument("--history", default="origin/main")
    ap.add_argument("--until", help="end of the history window (git date; default now)")
    ap.add_argument("--since", help="start of the history window (git date; default --days ago)")
    ap.add_argument("--closure", action="append", default=[])
    ap.add_argument("--profile", action="append", default=[], help="more peak TSVs (later wins)")
    ap.add_argument("--chain", action="store_true", help="print the capped critical chain")
    a = ap.parse_args()
    g = load_graph(a.rev)
    secs = load_secs(a.profile)
    rdeps = {m: [] for m in g}
    for m, imps in g.items():
        for d in imps:
            if d in rdeps:
                rdeps[d].append(m)
    up = {}
    for m in reversed(topo(g, g)):   # importers before imports
        s = {m}
        for r in rdeps[m]:
            s |= up[r]
        up[m] = s

    since = a.since or f"{a.days}.days"
    log = git("log", "--first-parent", f"--since={since}", *([f"--until={a.until}"] if a.until else []),
              "--name-status", "--format=@%H", a.history)
    per = []
    commit = None
    for line in log.splitlines() + ["@"]:
        if line.startswith("@"):
            if commit is not None:
                per.append(commit)
            commit = (line[1:], set(), set())
        elif line.strip():
            f = line.split("\t")
            st, path = f[0], f[-1]
            m = module_of(path)
            if not m:
                continue
            if st == "M" and m in g:
                commit[1].add(m)
            elif st[0] in "AMRC":
                commit[2].add(m)
    counts, seconds = [], []
    for _, modified, added in per:
        s = set()
        for m in modified:
            s |= up[m]
        s |= added
        counts.append(len(s))
        seconds.append(sum(secs.get(m, 60.0) for m in s))
    edges = sum(len(v) for v in g.values())
    pairs = sum(len(closure(g, m)) - 1 for m in g)
    print(f"graph: {len(g)} modules, {edges} internal import edges, {pairs} (module, import) pairs")
    if counts:
        print(f"rebuilds over {len(per)} commits ({a.days} days of {a.history}): total {sum(counts)} "
              f"modules, mean {statistics.mean(counts):.1f}, median {statistics.median(counts):.0f}; "
              f"recorded time {sum(seconds) / 3600:.1f} h")
    for name, mods in [("all", set(g))] + [(c, closure(g, c)) for c in a.closure]:
        t, chain = crit(g, secs, mods)
        t5, chain5 = crit(g, secs, mods, cap=300)
        print(f"critical path {name} ({len(mods)} modules): {t / 3600:.2f} h ({len(chain)} modules, "
              f"{chain[0]} -> {chain[-1]}); capped at 300 s: {t5 / 3600:.2f} h ({len(chain5)} modules, "
              f"{chain5[0]} -> {chain5[-1]})")
        if a.chain:
            for m in chain5:
                print(f"  {secs.get(m, 60.0):8.0f}s {m}")


if __name__ == "__main__":
    main()
