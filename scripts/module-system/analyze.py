#!/usr/bin/env python3
"""Replay main's Lean commits: per commit, the modules Lake rebuilds today (changed modules and
every transitive importer) and, with the module system (`public import` + `@[expose] public
section`), the changed modules plus the transitive importers of those whose public interface
changed. Interface (static estimate): the module's commands without comments, docstrings,
`example`s, `#`-commands and private theorems, with theorem/lemma proofs cut at the top-level `:=`.

usage: analyze.py REPO SINCE [PROFILE.tsv...] > commits.tsv
"""
import collections, re, subprocess, sys

repo, since = sys.argv[1], sys.argv[2]
END = "22f3190"
profiles = sys.argv[3:]
LIBS = (("FV/", ""), ("FVTest/", ""), ("corpus/dsl/", "corpus/dsl/"))


def git(*a, inp=None):
    return subprocess.run(["git", "-C", repo, *a], capture_output=True, input=inp, check=True).stdout


def modname(path):
    for pre, strip in LIBS:
        if path.startswith(pre) and path.endswith(".lean"):
            return path[len(strip):-5].replace("/", ".")
    if path in ("FV.lean", "FVTest.lean"):
        return path[:-5]
    return None


IMP = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(\S+)", re.M)


def strip_comments(t):
    out, i, n = [], 0, len(t)
    while i < n:
        c = t[i]
        if t.startswith("/-", i):
            d, i = 1, i + 2
            while i < n and d:
                if t.startswith("/-", i):
                    d, i = d + 1, i + 2
                elif t.startswith("-/", i):
                    d, i = d - 1, i + 2
                else:
                    i += 1
            continue
        if t.startswith("--", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
            continue
        if t.startswith("'\"'", i):
            out.append("'\"'"); i += 3; continue
        if c == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == "\\" else 1
            out.append(t[i:j + 1]); i = j + 1; continue
        out.append(c); i += 1
    return "".join(out)


START = re.compile(r"^(?=@\[|[A-Za-z_#«])", re.M)
MODS = re.compile(r"^(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|meta)\s+)*")


def skip_attrs(s):
    s = s.lstrip()
    while s.startswith("@["):
        d, j = 0, 0
        for j, ch in enumerate(s):
            d += ch == "["; d -= ch == "]"
            if d == 0:
                break
        s = s[j + 1:].lstrip()
    return s


def sig_end(s):
    d = 0
    for j, ch in enumerate(s):
        if ch in "([{⟨": d += 1
        elif ch in ")]}⟩": d -= 1
        elif d == 0 and s.startswith(":=", j):
            return j
        elif d == 0 and ch == "|" and j and s[j - 1] == "\n":
            return j
    return len(s)


def interface(text):
    body = strip_comments(text)
    cmds, pos = [], [m.start() for m in START.finditer(body)] + [len(body)]
    for a, b in zip(pos, pos[1:]):
        c = body[a:b]
        rest = skip_attrs(c)
        mods = MODS.match(rest).group(0)
        kw = rest[len(mods):].split(None, 1)[0] if rest[len(mods):].strip() else ""
        if kw.startswith("#") or kw == "example":
            continue
        if kw in ("theorem", "lemma"):
            if "private" in mods.split():
                continue
            c = c[:sig_end(c)]
        cmds.append(" ".join(c.split()))
    return cmds


prof = {}
for p in profiles:
    for line in open(p):
        f = line.rstrip("\n").split("\t")
        if len(f) >= 3 and not line.startswith("#"):
            prof[f[0]] = float(f[2])

commits = git("log", "--reverse", f"--since={since}", "--format=%H", END, "--",
              "FV/*.lean", "FVTest/*.lean", "corpus/dsl/*.lean", "FV.lean", "FVTest.lean").decode().split()
base = commits[0] + "^"


def cat(rev, paths):
    if not paths:
        return {}
    inp = "".join(f"{rev}:{p}\n" for p in paths).encode()
    out = git("cat-file", "--batch", inp=inp)
    res, i = {}, 0
    for p in paths:
        nl = out.index(b"\n", i)
        hdr = out[i:nl].split()
        if hdr[-1] == b"missing":
            res[p] = None; i = nl + 1; continue
        sz = int(hdr[2])
        res[p] = out[nl + 1:nl + 1 + sz].decode(errors="replace")
        i = nl + 1 + sz + 1
    return res


files = [p for p in git("ls-tree", "-r", "--name-only", base).decode().split("\n") if modname(p)]
src = cat(base, files)
imports = {modname(p): [m for m in IMP.findall(t)] for p, t in src.items()}


def importers():
    r = collections.defaultdict(list)
    for m, ds in imports.items():
        for d in ds:
            if d in imports:
                r[d].append(m)
    return r


def cone(roots, rev):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo.extend(rev.get(m, ()))
    return seen


print("commit\tdate\tsubject\tchanged\tadded\tiface_changed\tbase_n\tms_n\tbase_s\tms_s\tproof_only\tms1_n\tms1_s")
for c in commits:
    st = git("diff", "--no-renames", "--name-status", c + "^", c).decode().split("\n")
    full = any(l.split("\t")[-1] == "lean-toolchain" for l in st if l)
    if any(l.split("\t")[-1] == "lakefile.toml" for l in st if l):
        d = git("diff", c + "^", c, "--", "lakefile.toml").decode()
        full = full or any(k in d for k in ("leanOptions", "moreLeanArgs", "moreServerArgs", "globs", "srcDir"))
    changed, added, deleted = [], [], []
    for l in st:
        if not l:
            continue
        k, p = l.split("\t", 1)
        m = modname(p)
        if not m:
            continue
        (deleted if k == "D" else added if k == "A" else changed).append((m, p))
    old = cat(c + "^", [p for _, p in changed])
    new = cat(c, [p for _, p in changed + added])
    for m, _ in deleted:
        imports.pop(m, None)
    iface = set()
    for m, p in changed:
        if old[p] is None or interface(old[p]) != interface(new[p]):
            iface.add(m)
    for m, p in changed + added:
        imports[m] = IMP.findall(new[p])
    for m, _ in added:
        iface.add(m)
    rev = importers()
    mods = {m for m, _ in changed + added}
    b = set(imports) if full else cone(mods, rev)
    ms = set(imports) if full else (mods | cone(iface, rev))
    po = not full and not iface and not deleted
    ms1 = mods | {x for m in iface for x in rev.get(m, ())}
    subj = git("log", "-1", "--format=%cI\t%s", c).decode().strip().replace("\t", " ", 1)
    d, s = subj.split(" ", 1)
    print("\t".join(map(str, [c[:10], d, s[:70].replace("\t", " "), len(changed), len(added), len(iface),
                              len(b), len(ms), round(sum(prof.get(m, 0) for m in b)),
                              round(sum(prof.get(m, 0) for m in ms)), int(po), len(ms1), round(sum(prof.get(m, 0) for m in ms1))])))
    sys.stdout.flush()
