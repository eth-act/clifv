#!/usr/bin/env python3
"""Write the Lean library sources of REV into worktree DEST.

usage: state.py base|port REV DEST

base: FV/, FVTest/, corpus/dsl/ (and FV.lean, FVTest.lean) exactly as at REV.
port: the same, ported: every file is scripts/module-port.py's port of its REV version, merged
(3-way, per file) with the branch's fixes, i.e. the difference between port(main version) and the
branch version (BRANCH, default parithosh/module-system). Files the branch added (absent on main)
are kept. Conflicts are reported and abort.
"""
import importlib.util, os, pathlib, subprocess, sys, tempfile

variant, rev, dest = sys.argv[1], sys.argv[2], pathlib.Path(sys.argv[3])
REPO = pathlib.Path("/home/user/workspace/repo")
MAIN = os.environ.get("MAIN", "22f3190")
BRANCH = os.environ.get("BRANCH", "parithosh/module-system")
LIBS = ("FV/", "FVTest/", "corpus/dsl/")


def git(*a, inp=None):
    return subprocess.run(["git", "-C", str(REPO), *a], capture_output=True, check=True, input=inp).stdout


def files(r):
    out = git("ls-tree", "-r", "--name-only", r).decode().split("\n")
    return {p for p in out if p.endswith(".lean") and (p.startswith(LIBS) or p in ("FV.lean", "FVTest.lean"))}


_cache = {}


def preload(r, paths):
    paths = [p for p in paths if (r, p) not in _cache]
    if not paths:
        return
    inp = "".join(f"{r}:{p}\n" for p in paths).encode()
    out = git("cat-file", "--batch", inp=inp)
    i = 0
    for p in paths:
        nl = out.index(b"\n", i)
        hdr = out[i:nl].split()
        sz = int(hdr[2])
        _cache[(r, p)] = out[nl + 1:nl + 1 + sz].decode()
        i = nl + 1 + sz + 1


def show(r, p):
    if (r, p) not in _cache:
        preload(r, [p])
    return _cache[(r, p)]


want = files(rev)
have = {str(p.relative_to(dest)) for d in LIBS for p in (dest / d).rglob("*.lean")} | \
       {p for p in ("FV.lean", "FVTest.lean") if (dest / p).exists()}
preload(rev, sorted(want))
if variant == "base":
    for p in have - want:
        (dest / p).unlink()
    for p in want:
        t = show(rev, p)
        f = dest / p
        if not f.exists() or f.read_text() != t:
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text(t)
    sys.exit(0)

spec = importlib.util.spec_from_file_location("mp", REPO / "scripts/module-port.py")
mp = importlib.util.module_from_spec(spec); spec.loader.exec_module(mp)
mainf, branchf = files(MAIN), files(BRANCH)
preload(MAIN, sorted(mainf & want)); preload(BRANCH, sorted(branchf))
extra = branchf - mainf          # files the port added (CommonBits, SimprocAttr, ...)
want_p = want | extra
for p in have - want_p:
    (dest / p).unlink()
conflicts = []
for p in want_p:
    if p in extra:
        t = show(BRANCH, p)
    else:
        theirs = mp.port(show(rev, p))
        if p in mainf and p in branchf:
            base, ours = mp.port(show(MAIN, p)), show(BRANCH, p)
            if theirs == base:
                t = ours
            elif ours == base:
                t = theirs
            else:
                with tempfile.TemporaryDirectory() as d:
                    for n, s in (("o", ours), ("b", base), ("t", theirs)):
                        pathlib.Path(d, n).write_text(s)
                    r = subprocess.run(["git", "merge-file", "-p", f"{d}/o", f"{d}/b", f"{d}/t"],
                                       capture_output=True, text=True)
                    t = r.stdout
                    if r.returncode:
                        conflicts.append(p)
        else:
            t = theirs
    f = dest / p
    if not f.exists() or f.read_text() != t:
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(t)
if conflicts:
    sys.exit("conflicts: " + " ".join(conflicts))
