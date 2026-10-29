#!/usr/bin/env python3
"""addall.py < coreall-output : add `import all M` lines to each module's header."""
import pathlib, sys, re
ROOT = pathlib.Path("/home/user/workspace/repo")
for line in sys.stdin:
    if ":" not in line: continue
    mod, rest = line.split(":", 1)
    need = [x for x in rest.split() if x != "NOTBUILT"]
    if not need: continue
    p = ROOT / (mod.replace(".", "/") + ".lean")
    if mod.startswith("Corpus."): p = ROOT / "corpus/dsl" / (mod.replace(".", "/") + ".lean")
    ls = p.read_text().split("\n")
    have = {l.split()[-1] for l in ls if l.startswith("import all ")}
    add = [f"import all {m}" for m in need if m not in have]
    if not add: continue
    last = max(i for i, l in enumerate(ls[:300]) if re.match(r"^(public\s+)?(meta\s+)?import\s", l))
    ls[last + 1:last + 1] = add
    p.write_text("\n".join(ls))
    print(mod, len(add))
