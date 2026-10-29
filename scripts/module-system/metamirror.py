#!/usr/bin/env python3
"""metamirror.py FILE: add `meta import M` for every `public import M` / `import M` of FILE (for
native_decide / #eval / the interpreter, which need the imports' compiled code)."""
import re, sys, pathlib
p = pathlib.Path(sys.argv[1]); t = p.read_text()
imps = re.findall(r"^(?:public )?import (?!all )(\S+)\s*$", t, re.M)
have = set(re.findall(r"^(?:public )?meta import (\S+)", t, re.M))
add = [f"meta import {m}" for m in imps if m not in have]
if add:
    ls = t.split("\n")
    last = max(i for i, l in enumerate(ls[:300]) if re.match(r"^(public\s+)?(meta\s+)?import\s", l))
    ls[last + 1:last + 1] = add
    p.write_text("\n".join(ls))
print(len(add))
