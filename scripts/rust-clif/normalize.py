#!/usr/bin/env python3
"""Rewrite cg_clif's CLIF dumps into the text our tools accept, without changing semantics.

usage: normalize.py CLIF_DIR STAGE OUT [--lean-gv-order] [--drop-nop] [--split]
  CLIF_DIR  a `<crate>.clif/` directory written by cg_clif (scripts/rust-clif/dump.sh)
  STAGE     unopt | opt

All functions of the directory go into one file OUT (the `set`/`target` header of the first);
with `--split`, OUT is a directory and each function gets its own file (same header).
Rewrites (each is a pure renaming/inlining, checked by `clif-oracle check` on the result):
  * `function u0:N(`                     -> `function %SYM(`   (SYM from the `; symbol` line)
  * `fnK = [colocated] u0:N sigM ; …`    -> `fnK = [colocated] %SYM(<sigM inlined>)`
    SYM: the symbol of the corpus function numbered u0:N, else the quoted symbol in the
    comment, else `u0_N`; Cranelift libcalls `%Memcpy sigM` -> `%memcpy(<sigM>)` (the symbol the
    libcall relocates against; the reader would otherwise parse `%Memcpy` as `LibCall`).
  * `sigM = …` lines are dropped once no `call_indirect sigM` refers to them.
  * `gvK = symbol colocated userextnameJ ; allocX` -> `gvK = symbol colocated %allocX`
    (`%data_J` when the comment is not an alloc name, e.g. `; vtable`).
  * comment-only lines are dropped (cg_clif's `; abi …` comments are several KB each).
  * `--lean-gv-order`: write `colocated symbol %X` instead of the reader's `symbol colocated %X`,
    the order `FV/Clif/Parse.lean` expects (a discrepancy with the pinned reader); the result
    is then for the Lean tools only.
  * `--drop-nop`: drop `nop` (cg_clif emits it only as an anchor for comments).
"""

import re
import sys
from pathlib import Path


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    lean_gv = "--lean-gv-order" in sys.argv
    drop_nop = "--drop-nop" in sys.argv
    split = "--split" in sys.argv
    d, stage, out = Path(args[0]), args[1], Path(args[2])
    files = sorted(p for p in d.iterdir() if p.name.endswith(f".{stage}.clif"))
    texts = [p.read_text() for p in files]

    # u0:N -> symbol, over the whole directory (cg_clif numbers FuncIds module-wide).
    sym = {}
    for t in texts:
        m = re.search(r"^function u0:(\d+)\(", t, re.M)
        s = re.search(r"^; symbol (\S+)", t, re.M)
        if m and s:
            sym[m.group(1)] = s.group(1)

    header = []
    bodies = []
    for t in texts:
        lines = t.splitlines()
        start = next(i for i, l in enumerate(lines) if l.startswith("function "))
        if not header:
            header = [l for l in lines[:start] if l.startswith(("set ", "target ", "test "))]
        body = lines[start:]
        sigs = {}
        for l in body:
            m = re.match(r"\s+(sig\d+) = (.*?)\s*(;.*)?$", l)
            if m:
                sigs[m.group(1)] = m.group(2)
        used_indirect = set(re.findall(r"call_indirect(?:\.\w+)? (sig\d+)", t))
        out_lines = []
        for l in body:
            s = l.strip()
            if s.startswith(";") or not s or (drop_nop and s == "nop"):
                continue
            m = re.match(r"function u0:(\d+)\((.*)$", l)
            if m:
                l = f"function %{sym[m.group(1)]}({m.group(2)}"
            m = re.match(r"(\s+fn\d+ = )(colocated )?(u0:(\d+)|%(\w+)) (sig\d+)\s*(;\s*(.*))?$", l)
            if m:
                pre, coloc, _, num, libcall, sig, _, comment = m.groups()
                if libcall:
                    name = libcall.lower()
                elif num in sym:
                    name = sym[num]
                else:
                    q = re.match(r'"([^"]+)"', comment or "")
                    name = q.group(1) if q else f"u0_{num}"
                l = f"{pre}{coloc or ''}%{name}{sigs[sig]}"
            m = re.match(r"(\s+sig\d+) = ", l)
            if m and m.group(1).strip() not in used_indirect:
                continue
            m = re.match(r"(\s+gv\d+ = .*symbol (?:colocated )?)userextname(\d+)(\S*)\s*(;\s*(\S+))?", l)
            if m:
                pre, j, off, _, c = m.groups()
                name = c if c and re.fullmatch(r"alloc\d+", c) else f"data_{j}"
                l = f"{pre}%{name}{off}"
                if lean_gv:
                    l = l.replace("symbol colocated ", "colocated symbol ")
            out_lines.append(l)
        bodies.append("\n".join(out_lines))
    if split:
        out.mkdir(parents=True, exist_ok=True)
        for p, b in zip(files, bodies):
            (out / p.name).write_text("\n".join(header) + "\n\n" + b + "\n")
    else:
        out.write_text("\n".join(header) + "\n\n" + "\n\n".join(bodies) + "\n")


if __name__ == "__main__":
    main()
