#!/usr/bin/env python3
"""Project per-commit rebuild sets for the last 14 days of main on TODAY's import graph.

usage: project.py PORTED_TREE > projection.tsv

For each commit C (from commits.tsv), on the import graph of PORTED_TREE (which must have the
same module set as main 22f3190 plus the port's added modules):
  touched = modules C modified (C's added modules count only themselves: they have no importers
            when they are added),
  iface   = touched modules whose public interface changed (analyze.py's static estimate) plus
            added ones.
  base    = touched ∪ all transitive importers of touched              (Lake today)
  mech    = touched ∪ all transitive importers of iface                (module system, every
            import public: an importer sees everything re-exported transitively)
  private = touched ∪ {N : some module in vis(N) is in iface}, where vis(N) = N's direct imports
            plus everything they re-export (transitive `public import` closure) and transitive
            rebuild of N's own re-exporters only if N's interface changed (assumed not: a rebuilt
            module whose source did not change keeps its public .olean).
Seconds: sum of recorded module seconds (profile-ci.tsv, CI runner, ≈2× this orb).
"""
import collections, csv, pathlib, re, subprocess, sys

tree = pathlib.Path(sys.argv[1])
MS = pathlib.Path("/home/user/ms")
exec(open(MS / "analyze.py").read().split("prof = {}")[0].replace("repo, since = sys.argv[1], sys.argv[2]", "repo = '/home/user/workspace/repo'"))
exec("def cat" + open(MS / "analyze.py").read().split("def cat")[1].split("files = [")[0])

IMPK = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)", re.M)
mods, pub, allimp = {}, collections.defaultdict(set), collections.defaultdict(set)
for d in ("FV", "FVTest", "corpus/dsl/Corpus"):
    for p in (tree / d).rglob("*.lean"):
        rel = str(p.relative_to(tree))
        mods[modname(rel)] = p
for m, p in mods.items():
    for pubk, metak, allk, d in IMPK.findall(p.read_text()):
        if d in mods:
            allimp[m].add(d)
            if pubk:
                pub[m].add(d)
rev = collections.defaultdict(set)
for m, ds in allimp.items():
    for d in ds:
        rev[d].add(m)
# reexp[X] = X plus everything X re-exports transitively
reexp = {}
def rx(x):
    if x in reexp:
        return reexp[x]
    reexp[x] = {x}
    s = {x}
    for d in pub[x]:
        s |= rx(d)
    reexp[x] = s
    return s
sys.setrecursionlimit(100000)
for m in mods:
    rx(m)
# seen_by[X] = modules N with X in vis(N): N imports some Y with X ∈ reexp[Y]
exported_by = collections.defaultdict(set)   # X -> Ys that re-export X (incl. X)
for y, s in reexp.items():
    for x in s:
        exported_by[x].add(y)
def seen_by(x):
    out = set()
    for y in exported_by[x]:
        out |= rev[y]
    return out
def cone(roots):
    seen, todo = set(), list(roots)
    while todo:
        x = todo.pop()
        if x not in seen:
            seen.add(x); todo.extend(rev[x])
    return seen
UX = bool(__import__("os").environ.get("IFACE_UX"))


def interface_ux(text, wholesale):
    """interface(), and with un-exposed definitions: a `def` body is private unless the def is
    `@[expose]` (abbrevs and instances are exposed by default) or the file is wholesale exposed."""
    if wholesale:
        return interface(text)
    body = strip_comments(text)
    cmds, pos = [], [m.start() for m in START.finditer(body)] + [len(body)]
    for a, b in zip(pos, pos[1:]):
        c = body[a:b]
        rest = skip_attrs(c)
        attrs = c[:len(c) - len(rest)]
        mods = MODS.match(rest).group(0)
        kw = rest[len(mods):].split(None, 1)[0] if rest[len(mods):].strip() else ""
        if kw.startswith("#") or kw == "example":
            continue
        if kw in ("theorem", "lemma") or (kw == "def" and "expose" not in attrs):
            if "private" in mods.split():
                continue
            c = c[:sig_end(c)]
        cmds.append(" ".join(c.split()))
    return cmds


def iface_of(text, path):
    if not UX:
        return interface(text)
    f = tree / path
    whole = (not f.exists()) or bool(re.search(r"^@\[expose\] public section$", f.read_text(), re.M))
    return interface_ux(text, whole)


prof = {}
for line in open(MS / "profile-ci.tsv"):
    f = line.split("\t")
    if len(f) >= 3:
        prof[f[0]] = float(f[2])
import os
R = set(open(os.environ["RESTRICT"]).read().split()) if os.environ.get("RESTRICT") else None
secs = lambda s: round(sum(prof.get(m, 0) for m in s))
rows = list(csv.DictReader(open(MS / "commits.tsv"), delimiter="\t"))
print("commit\tsubject\ttouched\tiface\tbase_n\tmech_n\tpriv_n\tbase_s\tmech_s\tpriv_s")
for r in rows:
    c = r["commit"]
    st = git("diff", "--no-renames", "--name-status", c + "^", c).decode().split("\n")
    changed, added = [], []
    for l in st:
        if not l:
            continue
        k, p = l.split("\t", 1)
        m = modname(p)
        if not m or m not in mods:
            continue
        (added if k == "A" else changed if k == "M" else []).append((m, p))
    old = cat(c + "^", [p for _, p in changed]); new = cat(c, [p for _, p in changed])
    iface = {m for m, p in changed if old[p] is None or iface_of(old[p], p) != iface_of(new[p], p)}
    iface |= {m for m, _ in added}
    touched = {m for m, _ in changed} | {m for m, _ in added}
    mod_only = {m for m, _ in changed}
    base = cone(mod_only) | touched
    mech = cone(iface & mod_only) | touched
    priv = set(touched)
    for x in iface & mod_only:
        priv |= seen_by(x)
    if R is not None:
        base, mech, priv, touched = base & R, mech & R, priv & R, touched & R
    print("\t".join(map(str, [c, r["subject"][:60], len(touched), len(iface), len(base), len(mech),
                              len(priv), secs(base), secs(mech), secs(priv)])))
