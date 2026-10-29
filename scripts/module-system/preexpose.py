#!/usr/bin/env python3
"""Static pre-expose: expose every definition that another module of the closure names in an
unfolding tactic (`simp [..]`, `simp only [..]`, `simp_all [..]`, `simpa [..]`, `dsimp [..]`,
`unfold ..`, `delta ..`, `rw [..]`, `rwa [..]`, `erw [..]`, `simp_arith [..]`, `norm_num [..]`).
Uses expose.py's index and editing. usage: preexpose.py INDEX MODLIST
Prints category/name/module lines like expose.py ("static simp/unfold")."""
import collections, pathlib, re, subprocess, sys

ROOT = pathlib.Path("/home/user/workspace/repo")
idx, modlist = sys.argv[1], sys.argv[2]
mods = open(modlist).read().split()
by_short = collections.defaultdict(set)
kind = {}
for line in open(idx):
    f = line.rstrip("\n").split("\t")
    if len(f) < 4:
        continue
    kind[f[1]] = (f[0], f[3])
    p = f[1].split(".")
    for i in range(len(p)):
        by_short[".".join(p[i:])].add(f[1])
TAC = re.compile(r"\b(?:simp(?:_all|a|_arith)?(?:\s+only)?|dsimp(?:\s+only)?|rw|rwa|erw|norm_num)\b[^\[\n]*\[([^\]]*)\]|\b(?:unfold|delta)\s+([^\n]*)")
IDENT = re.compile(r"[A-Za-z_«][\w.'«»!?]*")
want = {}
for m in mods:
    p = ROOT / (m.replace(".", "/") + ".lean")
    if not p.exists():
        continue
    t = p.read_text()
    for tm in TAC.finditer(t):
        body = tm.group(1) if tm.group(1) is not None else tm.group(2).split(" at ")[0]
        for tok in IDENT.findall(body):
            tok = tok.lstrip("←")
            if tok in ("at", "only", "this", "h"):
                continue
            names = by_short.get(tok, set())
            names = {n for n in names if kind[n][0] != m and kind[n][1] == "def"}
            if 0 < len(names) <= 3:
                for n in names:
                    want.setdefault(n, m)
# write a fake log that expose.py understands: one "Invalid simp theorem" error per name
log = pathlib.Path("/tmp/ms_preexpose.log")
log.write_text("".join(f"error: {kind[n][0].replace('.', '/')}.lean:1:0: Invalid simp theorem `{n}`: Expected a definition with an exposed body\n"
                       for n in sorted(want)))
r = subprocess.run(["python3", "/home/user/ms/expose.py", idx, str(log)], capture_output=True, text=True)
print(r.stdout.replace("simp/unfold\t", "static simp/unfold\t"), end="")
