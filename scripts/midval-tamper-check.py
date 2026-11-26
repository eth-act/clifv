#!/usr/bin/env python3
"""#1119 layer 2: negative end-to-end test of `link-check`'s mid-end validator check.

usage: midval-tamper-check.py BUNDLE_DIR [--link-check PATH] [--work DIR]

BUNDLE_DIR is a `cargo fv link-proof` directory (`target/fv/<mode>/bin-check/<tag>`, kept by
`--keep-temps`) of a `--midval` build with at least one function compiled from Cranelift's
optimised dump (`src_dump` in `bundle.json`).

1. `link-check BUNDLE_DIR --dead-cleanup --prune` as cargo fv's binary check runs it: every pair
   holds (`the pair fails for 0`: `Link.midPairB`, or the hoisting mode's `Link.hoistCopy` at the
   image's symbol table), N of N functions pass, and the theorem named is a `_mid` (or `_midS`)
   one.
2. A copy whose `bundle.json` points one such function A's `src_dump` at another function B's
   unoptimised dump of the same codegen unit, renamed to A (its own `u0:` identity, `; decl` and
   `; symbol` lines): the bundle now says that A's optimised code came from B's source. `link-check`
   must reject exactly A's pair (`the pair fails for 1`, A's `FAIL` lines name
   `Link.midPairB`), prune A and its callers (fewer than N pass), so cargo fv's binary check
   does not count the executable verified (`cargo-fv/src/bincheck.rs`: `pass < total`).

Exit 0 when both hold; prints what it ran and saw.
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def run_check(link_check, d):
    p = subprocess.run([str(link_check), str(d), "--dead-cleanup", "--prune"], capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def prune_counts(out):
    m = re.search(r"--prune: (\d+) of (\d+) functions pass", out)
    return (int(m.group(1)), int(m.group(2))) if m else None


def mid_fails(out):
    # the pairs link-check rejects: `Link.midPairB` and the hoisting mode's `Link.hoistCopy` both
    m = re.search(r"the pair fails for (\d+)", out)
    return int(m.group(1)) if m else None


def own_id(text, sym):
    """The dump's own function identity (`u0:N`) and its declaration line."""
    m = re.search(r"^function (u0:\d+)\(", text, re.M)
    if not m:
        return None, None
    fid = m.group(1)
    d = re.search(r"^; decl " + re.escape(fid) + r' func (\S+) "' + re.escape(sym) + r'"$', text, re.M)
    return fid, (d.group(0) if d else None)


def renamed(b_text, b_sym, a_text, a_sym):
    """B's dump as a dump of A: B's own identity, declaration and `; symbol` lines made A's."""
    a_id, a_decl = own_id(a_text, a_sym)
    b_id, b_decl = own_id(b_text, b_sym)
    if not (a_id and a_decl and b_id and b_decl):
        return None
    t = b_text.replace(b_decl, a_decl)
    t = re.sub(re.escape(b_id) + r"\b", a_id, t)
    t = re.sub(r"^; symbol " + re.escape(b_sym) + r"$", "; symbol " + a_sym, t, flags=re.M)
    return t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bundle_dir", type=Path)
    ap.add_argument("--link-check", type=Path, default=Path(__file__).resolve().parent.parent / ".lake/build/bin/link-check")
    ap.add_argument("--work", type=Path, default=None)
    a = ap.parse_args()
    bj = json.loads((a.bundle_dir / "bundle.json").read_text())

    rc, out = run_check(a.link_check, a.bundle_dir)
    pc = prune_counts(out)
    theorem = next((l.strip() for l in out.splitlines() if l.strip().startswith("theorem: ")), "")
    print(f"as written: rc={rc}, the pair fails for {mid_fails(out)}, --prune {pc}, {theorem[:120]}")
    ok1 = mid_fails(out) == 0 and pc is not None and pc[0] == pc[1] and "_mid" in theorem
    if not ok1:
        print(out[-3000:])
        print("FAIL: the bundle as written does not pass with a _mid theorem")
        return 1

    # A: a function with src_dump; B: another function of A's unit (its unoptimised dump)
    pick = None
    for ui, u in enumerate(bj["units"]):
        fns = u["functions"]
        for fa in fns:
            if "src_dump" not in fa:
                continue
            a_text = Path(fa["src_dump"]).read_text()
            for fb in fns:
                if fb["name"] == fa["name"]:
                    continue
                b_text = Path(fb.get("src_dump", fb["dump"])).read_text()
                t = renamed(b_text, fb["name"], a_text, fa["name"])
                if t is not None and t != a_text:
                    pick = (ui, fa, fb, t)
                    break
            if pick:
                break
        if pick:
            break
    if not pick:
        print("FAIL: no function with src_dump that shares its unit with another function")
        return 1
    ui, fa, fb, t = pick
    work = Path(a.work or tempfile.mkdtemp(prefix="midval-tamper-"))
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(a.bundle_dir, work)
    src = work / "tampered.unopt.clif"
    src.write_text(t)
    for f in bj["units"][ui]["functions"]:
        if f["name"] == fa["name"]:
            f["src_dump"] = str(src)
    (work / "bundle.json").write_text(json.dumps(bj))
    print(f"tampered: {fa['name']}'s src_dump := {fb['name']}'s unoptimised dump renamed to it ({src})")

    rc, out = run_check(a.link_check, work)
    pc2 = prune_counts(out)
    lines = out.splitlines()
    # link-check names a function by its linked name (`final`: a local symbol renamed `__fv_<tag>_…`)
    a_names = {f"FAIL {fa['name']}:", f"FAIL {fa.get('final', fa['name'])}:"}
    fail_a = [i for i, l in enumerate(lines) if l.strip() in a_names]
    a_mid = any("Link.midPairB" in lines[j] for i in fail_a for j in range(i + 1, min(i + 8, len(lines))) if lines[j].startswith("      "))
    theorem = next((l.strip() for l in lines if l.strip().startswith("theorem: ")), "")
    print(f"tampered: rc={rc}, the pair fails for {mid_fails(out)}, {fa['name']} fails Link.midPairB: {a_mid}, --prune {pc2}, {theorem[:120]}")
    ok2 = mid_fails(out) == 1 and a_mid and pc2 is not None and pc2[1] == pc[1] and pc2[0] < pc2[1]
    if not ok2:
        print(out[-3000:])
        print("FAIL: link-check did not reject the tampered pair")
        return 1
    print(f"OK: link-check rejects the tampered src_dump ({pc2[0]} of {pc2[1]} functions pass: the executable is not verified)")
    if a.work is None:
        shutil.rmtree(work)
    return 0


if __name__ == "__main__":
    sys.exit(main())
