#!/usr/bin/env python3
"""Run-test files from the static scan's flagged functions (UninitSem, #537).

    gen_uninit_runtests.py RESULT.json OUTDIR [GROUP...]

Leaf functions (no fnN/sigN declarations) with integer parameters/returns only, each renamed
%fK and given run lines on a few argument tuples. The expectation is a placeholder: compare
Clif.run (`clif-filetest --zero-slots --oracle-dir`) with the Cranelift interpreter (agree /
disagree counts), not with the expectation.
"""
import json, os, re, sys

ROOT = "/home/kev/work/fv-compiler-rust"
INT = {"i8", "i16", "i32", "i64"}
ARGS = [0, 1, 2, 7, -1]


def main():
    res, out, groups = sys.argv[1], sys.argv[2], sys.argv[3:] or ["fv-demo", "survey", "deps"]
    d = json.load(open(res))
    os.makedirs(out, exist_ok=True)
    seen, n = set(), 0
    for g in groups:
        chunks = []
        for f in d[g]["findings"]:
            if f["file"] in seen:
                continue
            seen.add(f["file"])
            src = open(os.path.join(ROOT, f["file"])).read()
            body = src[src.index("function "):]
            m = re.match(r"function %(\S+?)\(([^)]*)\)(?: -> ([^{]*?))? system_v \{", body)
            if not m or re.search(r"^\s*(fn|sig|gv)\d+ = ", body, re.M):
                continue
            ps = [p.strip() for p in m.group(2).split(",") if p.strip()]
            rs = [r.strip() for r in (m.group(3) or "").split(",") if r.strip()]
            if not all(p in INT for p in ps) or not all(r in INT for r in rs) or not rs:
                continue
            name = f"f{n}"
            n += 1
            body = body.replace(f"%{m.group(1)}(", f"%{name}(", 1)
            runs = []
            for a in ARGS:
                args = ", ".join(str(a) for _ in ps)
                exp = ", ".join("0" for _ in rs)
                runs.append(f"; run: %{name}({args}) == [{exp}]" if len(rs) > 1 else f"; run: %{name}({args}) == {exp}")
            chunks.append(body.rstrip() + "\n" + "\n".join(runs) + "\n")
        for i in range(0, len(chunks), 50):
            with open(os.path.join(out, f"{g}-{i // 50}.clif"), "w") as fh:
                fh.write("test interpret\ntest run\ntarget aarch64\n\n" + "\n".join(chunks[i:i + 50]))
    print(f"{n} functions")


main()
