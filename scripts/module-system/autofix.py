#!/usr/bin/env python3
"""Apply the module-system fixes Lean's error messages name, for one build log per argument.

  * "consider adding `public meta import M`"            -> add `public meta import M`
  * "Invalid `meta` definition `D`, `X` not marked `meta`" (X defined in this file)
                                                          -> mark X's definition `meta`
Prints what it did; leaves anything else alone.
"""
import pathlib, re, sys

ROOT = pathlib.Path("/home/user/workspace/repo")
DEF = r"^(\s*)((?:@\[[^\]]*\]\s*)*)((?:private |protected |noncomputable |partial |unsafe |nonrec )*)(def|abbrev|instance|structure|inductive|opaque|register_option|theorem)\s+"


def add_import(path, line):
    t = path.read_text()
    if re.search(rf"^{re.escape(line)}\s*$", t, re.M):
        return False
    ls = t.split("\n")
    last = max(i for i, l in enumerate(ls[:200]) if re.match(r"^(public\s+)?(meta\s+)?import\s", l))
    ls.insert(last + 1, line)
    path.write_text("\n".join(ls))
    return True


def mark_meta(path, name):
    t = path.read_text()
    short = name.split(".")[-1]
    pat = re.compile(DEF + r"((?:[\w.«»']+\.)?" + re.escape(short) + r")(?=[\s:(\[{]|$)", re.M)
    for m in pat.finditer(t):
        full = m.group(5)
        if not (name.endswith(full) or full.endswith(short)):
            continue
        if "meta " in m.group(3):
            return False
        mods = m.group(3)
        vis = re.match(r"(?:private |protected )*", mods).group(0)
        s = m.start(3) + len(vis)
        t = t[:s] + "meta " + t[s:]
        path.write_text(t)
        return True
    return False


for log in sys.argv[1:]:
    txt = pathlib.Path(log).read_text(errors="replace")
    for m in re.finditer(r"^error: ([^:\n]+\.lean):\d+:\d+: (.*?)(?=^error|^warning|^info|\Z)", txt, re.M | re.S):
        f, msg = ROOT / m.group(1), m.group(2)
        for imp in re.findall(r"consider adding `(public meta import [\w.]+)`", msg):
            if add_import(f, imp):
                print(f"{m.group(1)}: + {imp}")
        if "exported from the current module" in msg and "definitional equality" in msg:
            # term-mode `rfl` of an exported theorem elaborates in the public scope (only exposed
            # bodies unfold); `by rfl` elaborates the proof privately
            L = int(re.search(rf"^error: {re.escape(m.group(1))}:(\d+):", m.group(0), re.M).group(1)) - 1
            ls = f.read_text().split("\n")
            for k in range(L, min(L + 6, len(ls))):
                if re.search(r":=\s*rfl\s*$", ls[k]):
                    ls[k] = re.sub(r":=\s*rfl\s*$", ":= by rfl", ls[k])
                    f.write_text("\n".join(ls))
                    print(f"{m.group(1)}:{k + 1}: := rfl -> := by rfl")
                    break
        if "neither marked nor imported as `meta`" in msg:
            if add_import(f, "public meta import Lean.Meta.Tactic.Simp.BuiltinSimprocs"):
                print(f"{m.group(1)}: + public meta import Lean.Meta.Tactic.Simp.BuiltinSimprocs")
        for x in re.findall(r"`([^`]+)` not marked `meta`", msg):
            if mark_meta(f, x):
                print(f"{m.group(1)}: meta {x}")
