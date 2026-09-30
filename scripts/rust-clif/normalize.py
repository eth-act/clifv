#!/usr/bin/env python3
"""Rewrite cg_clif's CLIF dumps into the text our tools accept, without changing semantics.

usage: normalize.py CLIF_DIR STAGE OUT [--drop-nop] [--split] [--strip-srcloc] [--gvmap F] [--fnmap F]
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
  * `--drop-nop`: drop `nop` (cg_clif emits it only as an anchor for comments).
  * `--fnmap F` (`u0:N<TAB>symbol` lines, `clif-data-export --fnmap`): names the `u0:N` callees
    of other crates/codegen units (their comment is an `Instance`, not a symbol) instead of `u0_N`.
  * `--strip-srcloc`: drop the `@XXXX` source-location prefix of instructions (cg_clif writes
    one per instruction with debuginfo on, e.g. under cargo's dev profile; `cargo fv`).
"""

import re
import sys
from pathlib import Path


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    drop_nop = "--drop-nop" in sys.argv
    split = "--split" in sys.argv
    strip_srcloc = "--strip-srcloc" in sys.argv
    flags = [a for a in sys.argv[1:] if a.startswith("--")]
    gvmap = {}
    for i, a in enumerate(flags):
        if a == "--gvmap":
            for line in open(sys.argv[sys.argv.index("--gvmap") + 1]):
                if not line.strip():  # an empty map is a single blank line
                    continue
                stem, gv, name = line.rstrip("\n").split("\t")
                gvmap[(stem, gv)] = name.removeprefix("%")
    fnmap = {}
    if "--fnmap" in sys.argv:
        for line in open(sys.argv[sys.argv.index("--fnmap") + 1]):
            if line.strip():
                n, name = line.rstrip("\n").split("\t")
                fnmap[n.removeprefix("u0:")] = name
    data_file = None
    if "--data-file" in sys.argv:
        data_file = Path(sys.argv[sys.argv.index("--data-file") + 1]).read_text()
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
    for f in files:
        t = texts[files.index(f)]
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
        # File-global sig renumbering: the dumps scope `sigN` per function (and re-declare
        # the same name per call_indirect site); the readers scope it per FILE, so the
        # merged file has duplicate entities. Per function chunk: dedup the declarations
        # (first wins) and renumber to fresh file-global indices, updating the
        # `call_indirect sigK` references to match; a declaration no `call_indirect` uses
        # is dropped.
        chunks = []
        cur = []
        for l in body:
            if l.startswith("function ") and cur:
                chunks.append(cur)
                cur = []
            cur.append(l)
        if cur:
            chunks.append(cur)
        gcount = 0
        out_lines = []
        for ch in chunks:
            if not any(l.startswith("function ") for l in ch):
                out_lines += ch
                continue
            local_g = {}
            for l in ch:
                ms = re.match(r"\s+(sig\d+) = ", l)
                if ms and ms.group(1) not in local_g:
                    local_g[ms.group(1)] = f"sig{gcount}"
                    gcount += 1
            used_here = set()
            for l in ch:
                if "call_indirect" in l:
                    for nm2 in re.findall(r"\b(sig\d+)\b", l):
                        used_here.add(local_g.get(nm2, nm2))
            decl_seen = set()
            for l0 in ch:
                if strip_srcloc:
                    l0 = re.sub(r"^@[0-9a-f]+(?=\s)", "", l0)
                s = l0.strip()
                if s.startswith(";") or not s or (drop_nop and s == "nop"):
                    continue
                l = re.sub(r"\bsig\d+\b", lambda m2: local_g.get(m2.group(0), m2.group(0)), l0)
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
                        name = q.group(1) if q else fnmap.get(num, f"u0_{num}")
                    l = f"{pre}{coloc or ''}%{name}{sigs[sig]}"
                m = re.match(r"(\s+sig\d+) = ", l)
                if m:
                    if m.group(1).strip() not in used_here:
                        continue
                m = re.match(r"(\s+)gv(\d+) = symbol (colocated )?userextname(\d+)(\S*)(\s*;.*)?$", l)
                if m:
                    ind, gv, coloc, j, off, _c = m.groups()
                    name = gvmap.get((f.name, f"gv{gv}"))
                    if name is None:
                        c = _c.strip("; ").strip() if _c else ""
                        name = c if re.fullmatch(r"alloc\d+", c) else f"data_{j}"
                    l = f"{ind}gv{gv} = symbol {coloc or ''}%{name}{off}"
                out_lines.append(l)
        bodies.append("\n".join(out_lines))
    if split:
        out.mkdir(parents=True, exist_ok=True)
        for p, b in zip(files, bodies):
            (out / p.name).write_text("\n".join(header) + "\n\n" + b + "\n")
    else:
        data = (data_file.rstrip("\n") + "\n") if data_file else ""
        out.write_text("\n".join(header) + "\n" + data + "\n\n".join(bodies) + "\n")


if __name__ == "__main__":
    main()
