#!/usr/bin/env python3
"""Which functions of a `cargo fv` executable a run actually executes, per crate: Lean-compiled
(a `__fvlean$` marker at the function's address) or other code (cg_clif fallbacks, std).

    scripts/fv-exec-trace.py EXE [program/test-harness args…]

EXE is an executable `cargo fv` linked with `--keep-temps` (its link map is
`target/fv/<mode>/tmp/link-<tag>.map`, which attributes each function to its input object,
i.e. its crate). The program runs under `qemu-aarch64-static -d exec,nochain`; every executed
translation block's address is mapped to its function. Combined with `--trap-replaced` (where
cg_clif's copy of every Lean-compiled function is a trap) this shows, per dependency crate,
how many Lean-compiled functions the run executed. Example (docs/USAGE.md):

    cargo fv test --no-run --trap-replaced --keep-temps
    scripts/fv-exec-trace.py target/fv/plain-trap/…/crates-<hash> --test-threads=1
"""
import bisect, collections, os, re, subprocess, sys, tempfile


def fnv_tag(s):  # pipeline::tag_of
    h = 0xCBF29CE484222325
    for b in s.encode():
        h = ((h ^ b) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"{h & 0xFFFFFFFFFFFF:012x}"


def find_map(exe):
    d = os.path.dirname(exe)
    while d != "/":
        cand = os.path.join(d, "tmp", f"link-{fnv_tag(exe)}.map")
        if os.path.exists(cand):
            return cand
        d = os.path.dirname(d)
    sys.exit(f"no link map for {exe} (build with `cargo fv … --keep-temps`)")


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    exe, args = os.path.abspath(sys.argv[1]), sys.argv[2:]
    mapf = find_map(exe)
    funcs, markers = [], set()
    for l in subprocess.run(["nm", "-S", exe], capture_output=True, text=True, check=True).stdout.splitlines():
        p = l.split()
        if p[-1].startswith("__fvlean$"):
            markers.add(int(p[0], 16))
        elif len(p) == 4 and p[2] in "tTwW" and int(p[1], 16) > 0:
            funcs.append((int(p[0], 16), int(p[0], 16) + int(p[1], 16)))
    funcs.sort()
    starts = [f[0] for f in funcs]
    inputs, in_text = [], False
    with open(mapf) as fh:
        for l in fh:
            m = re.match(r"\s*([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)\s+\d+( +)(.*)$", l)
            if not m:
                continue
            if len(m.group(3)) <= 1:
                in_text = m.group(4).startswith(".text")
            elif len(m.group(3)) <= 9 and in_text and int(m.group(2), 16) > 0:
                f = m.group(4)
                f = f[: f.rfind(":(")] if ":(" in f else f
                if f.endswith(")") and "(" in f:
                    f = f[: f.index("(")]
                inputs.append((int(m.group(1), 16), int(m.group(1), 16) + int(m.group(2), 16), f))
    inputs.sort()
    istarts = [i[0] for i in inputs]

    def crate_of(a):
        i = bisect.bisect_right(istarts, a) - 1
        if i < 0 or a >= inputs[i][1]:
            return "?"
        f = inputs[i][2]
        if "/lib/rustlib/" in f:
            return "(std, prebuilt)"
        n = f.rsplit("/", 1)[-1]
        m = re.match(r"lib(.+?)-[0-9a-f]+\.rlib$", n) or re.match(r"(.+?)-[0-9a-f]+\..*\.rcgu\.o$", n)
        return m.group(1) if m else n

    with tempfile.TemporaryDirectory(prefix="fv-exec-trace.") as tmp:
        log = os.path.join(tmp, "qemu.log")
        r = subprocess.run(["qemu-aarch64-static", "-d", "exec,nochain", "-D", log, exe] + args, capture_output=True, text=True)
        out = r.stdout.strip().splitlines()
        print(f"{out[-1] if out else ''} (exit {r.returncode})")
        pcs = set()
        with open(log, errors="replace") as fh:
            for l in fh:
                m = re.search(r"\[[0-9a-f]+/([0-9a-f]+)/", l)
                if m:
                    pcs.add(int(m.group(1), 16))
    lean, other = collections.defaultdict(set), collections.defaultdict(set)
    for pc in pcs:
        i = bisect.bisect_right(starts, pc) - 1
        if i < 0 or pc >= funcs[i][1]:
            continue
        s = funcs[i][0]
        (lean if s in markers else other)[crate_of(s)].add(s)
    print(f"{'crate':<22} {'Lean-compiled fns executed':>27} {'other fns executed':>19}")
    for c in sorted(set(lean) | set(other)):
        print(f"{c:<22} {len(lean[c]):>27} {len(other[c]):>19}")
    sys.exit(r.returncode)


main()
