#!/usr/bin/env python3
"""Classify the branch's per-file changes beyond the mechanical port of main.

For every .lean file: mech = module-port.py's port of main's version; branch = the branch's
version. Counts files whose branch version differs from mech, by kind of differing line:
  privatize : import lines only, from the shake step (public import -> import, added imports)
  meta      : `meta` added to declarations / sections, `meta import`s
  import all: `import all` lines
  expose    : changes to `@[expose]`/`public section`/`section`/`end` structure
  proof     : any other line (proof or declaration edits)
"""
import importlib.util, pathlib, re, subprocess, sys, difflib, collections

REPO = pathlib.Path("/home/user/workspace/repo")
MAIN, BRANCH = "22f3190", sys.argv[1] if len(sys.argv) > 1 else "parithosh/module-system"
spec = importlib.util.spec_from_file_location("mp", REPO / "scripts/module-port.py")
mp = importlib.util.module_from_spec(spec); spec.loader.exec_module(mp)
git = lambda *a: subprocess.run(["git", "-C", str(REPO), *a], capture_output=True, check=True).stdout.decode()
files = lambda r: {p for p in git("ls-tree", "-r", "--name-only", r).split("\n")
                   if p.endswith(".lean") and p.startswith(("FV/", "FVTest/", "corpus/dsl/"))}
mf, bf = files(MAIN), files(BRANCH)
kinds = collections.Counter(); per = collections.defaultdict(set); lines = collections.Counter()
for p in sorted(mf & bf):
    a = mp.port(git("show", f"{MAIN}:{p}")).split("\n")
    b = git("show", f"{BRANCH}:{p}").split("\n")
    if a == b:
        continue
    ks = set()
    for l in difflib.unified_diff(a, b, lineterm="", n=0):
        if l.startswith(("+++", "---", "@@")) or not l[1:].strip():
            continue
        s = l[1:].strip()
        if s.startswith("--"):
            k = "comment"
        elif re.match(r"(public )?meta import ", s) or re.search(r"\bmeta (def|partial|section|abbrev|instance)|public meta section|^meta$", s) \
                or (l[0] == "-" and False):
            k = "meta"
        elif s.startswith("import all "):
            k = "import all"
        elif re.match(r"(public )?import ", s):
            k = "imports"
        elif re.match(r"(@\[expose\] )?(public )?(meta )?section$|^end( \S+)?$|^namespace ", s):
            k = "section/expose"
        else:
            # a declaration line that only lost/gained `meta`
            k = "meta" if "meta" in s and l[0] == "+" else "proof/decl"
        ks.add(k); lines[k] += 1
    for k in ks:
        kinds[k] += 1; per[k].add(p)
added = sorted(bf - mf)
print(f"files: main {len(mf)}, branch {len(bf)} (added {len(added)}: {', '.join(added)})")
print("files differing from the mechanical port, by kind of change (a file can have several):")
for k, n in kinds.most_common():
    print(f"  {k:15s} {n:5d} files, {lines[k]:6d} lines")
print("proof/decl files:", ", ".join(sorted(per["proof/decl"])))
