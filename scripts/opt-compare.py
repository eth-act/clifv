#!/usr/bin/env python3
"""Compare two builds of `clif-opt` (e.g. before/after a mid-end change) on the difftest inputs.

usage: scripts/opt-compare.py CLIF_OPT_A CLIF_OPT_B [--out DIR] [--jobs N] [FILE.clif ...]

Inputs (without FILE arguments): corpus/clif/*.clif and corpus/clif/extrt/*.clif (corpus),
Cranelift's runtests/*.clif (runtests), and the `cargo fv` split dumps
examples/{survey,fv-demo}/target/fv/*/tmp/*/split/*.unopt.clif of the repository and of
$FV_DUMP_ROOT (survey). Each file is optimised by both binaries with the default configuration,
`--opt-proven-only` and `--opt-rules hand`, with `--stats`.

Per file and configuration the outputs are classified as
  same     byte-identical output and identical `--stats` lines;
  renum    identical `--stats` lines, and the outputs are equal after renaming the values of each
           function in order of first occurrence (`v12, v7, v12` and `v3, v9, v3` both become
           `v0, v1, v0`): the same functions up to a bijective renumbering of values;
  DIFF     anything else (listed with the work files kept in DIR).
Exit status 0 iff there is no DIFF.
"""
import argparse
import concurrent.futures
import glob
import hashlib
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONFIGS = [("default", []), ("proven", ["--opt-proven-only"]), ("hand", ["--opt-rules", "hand"])]
VALUE = re.compile(r"\bv[0-9]+\b")


def inputs():
    sets = []
    for f in sorted(glob.glob(f"{ROOT}/corpus/clif/*.clif") + glob.glob(f"{ROOT}/corpus/clif/extrt/*.clif")):
        sets.append(("corpus", f))
    rt = f"{ROOT}/third_party/wasmtime/cranelift/filetests/filetests/runtests"
    for f in sorted(glob.glob(f"{rt}/*.clif")):
        sets.append(("runtests", f))
    roots = [ROOT] + ([os.environ["FV_DUMP_ROOT"]] if os.environ.get("FV_DUMP_ROOT") else [])
    seen = set()
    for r in roots:
        for ex in ("survey", "fv-demo"):
            for f in sorted(glob.glob(f"{r}/examples/{ex}/target/fv/*/tmp/*/split/*.unopt.clif")):
                if f not in seen:
                    seen.add(f)
                    sets.append(("survey", f))
    return sets


def renumber(text):
    """Rename the values of each function in order of first occurrence."""
    out, names = [], {}
    for line in text.splitlines():
        if line.startswith("function "):
            names = {}
        out.append(VALUE.sub(lambda m: names.setdefault(m.group(0), f"v{len(names)}"), line))
    return "\n".join(out)


def run(binary, opts, f, dst):
    p = subprocess.run([binary, *opts, "--stats", f, dst], capture_output=True, text=True)
    text = open(dst).read() if os.path.exists(dst) else ""
    stats = sorted(l for l in p.stderr.splitlines() if l.startswith("%"))
    return p.returncode, text, stats, p.stderr


def compare(a, b, out, job):
    set_, f, (cfg, opts) = job
    key = hashlib.md5(f"{cfg}|{f}".encode()).hexdigest()[:16]
    pa, pb = f"{out}/{key}.a.clif", f"{out}/{key}.b.clif"
    ra, ta, sa, ea = run(a, opts, f, pa)
    rb, tb, sb, eb = run(b, opts, f, pb)
    if ra == rb and sa == sb and ta == tb:
        status = "same"
    elif ra == rb and sa == sb and renumber(ta) == renumber(tb):
        status = "renum"
    else:
        status = "DIFF"
        open(f"{out}/{key}.a.err", "w").write(ea)
        open(f"{out}/{key}.b.err", "w").write(eb)
    if status != "DIFF":
        for p in (pa, pb):
            if os.path.exists(p):
                os.remove(p)
    return status, set_, cfg, len(sa), f, key


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("a")
    ap.add_argument("b")
    ap.add_argument("files", nargs="*")
    ap.add_argument("--out", default="/tmp/opt-compare")
    ap.add_argument("--jobs", type=int, default=6)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    files = [("files", f) for f in args.files] if args.files else inputs()
    jobs = [(s, f, c) for s, f in files for c in CONFIGS]
    counts = {}
    diffs = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        for status, set_, cfg, nf, f, key in ex.map(lambda j: compare(args.a, args.b, args.out, j), jobs):
            c = counts.setdefault((set_, cfg, status), [0, 0])
            c[0] += 1
            c[1] += nf
            if status == "DIFF":
                diffs.append((set_, cfg, f, key))
    print(f"{len(files)} files")
    print("set\tconfig\tstatus\tfiles\tfunctions")
    for (set_, cfg, status), (n, nf) in sorted(counts.items()):
        print(f"{set_}\t{cfg}\t{status}\t{n}\t{nf}")
    for set_, cfg, f, key in diffs:
        print(f"DIFF {set_} {cfg} {f} ({args.out}/{key}.*)")
    return 1 if diffs else 0


if __name__ == "__main__":
    sys.exit(main())
