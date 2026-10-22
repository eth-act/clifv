#!/usr/bin/env python3
"""Axiom audit of the compiler theorems: run the `#print axioms` files in scripts/audit/ (or the
given files) through Lean and check that every listed theorem depends on no axiom other than
propext, Classical.choice and Quot.sound (docs/TO-PROVE.md §7, "Gate policy").

usage: scripts/axiom-audit.py [--log-dir DIR] [--cwd PKG] [FILE.lean...]

Run from the worktree root after the build (`lake build FV`): each file goes through
`lake env lean` in the worktree root, or in the Lake package PKG (relative to the root) with
`--cwd PKG` (`--cwd float-spec float-spec/audit.lean`: the FloatLib equality proofs, built by
scripts/float-spec.sh). A line `#print axioms X -- witness: native_decide` marks a non-vacuity witness,
which may also depend on the auxiliary axioms `native_decide` adds (`X._native.native_decide.ax_…`);
compiler theorems may not. One line per file: theorems reported / `#print axioms` commands, Lean
errors, disallowed axioms. Exit status 0 iff every file compiles, reports every theorem, and no
disallowed axiom appears.
"""
import argparse, pathlib, re, subprocess, sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ROOT = pathlib.Path(__file__).resolve().parent.parent
NATIVE = re.compile(r"[\w.'«»]+\._native\.native_decide\.ax_\w+")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("files", nargs="*")
    ap.add_argument("--log-dir", help="write each file's Lean output to DIR/<name>.log")
    ap.add_argument("--cwd", default=".", help="Lake package to run `lake env lean` in")
    a = ap.parse_args()
    cwd = ROOT / a.cwd
    files = [pathlib.Path(f).resolve() for f in a.files] or sorted((ROOT / "scripts/audit").glob("*.lean"))
    if a.log_dir:
        pathlib.Path(a.log_dir).mkdir(parents=True, exist_ok=True)
    bad = 0
    for f in files:
        text = f.read_text()
        wanted = len(re.findall(r"^#print axioms\s", text, re.M))
        witnesses = set(re.findall(r"^#print axioms\s+(\S+)\s+--\s*witness: native_decide", text, re.M))
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=cwd, capture_output=True, text=True)
        out = r.stdout + r.stderr
        if a.log_dir:
            (pathlib.Path(a.log_dir) / f"{f.stem}.log").write_text(out)
        flat = " ".join(out.split())
        deps = re.findall(r"'(.+?)' depends on axioms: \[([^\]]*)\]", flat)
        clean = re.findall(r"'(.+?)' does not depend on any axioms", flat)
        other = set()
        for thm, ax in deps:
            for x in (x.strip() for x in ax.split(",")):
                if x in STANDARD or (thm in witnesses and NATIVE.fullmatch(x)):
                    continue
                other.add(f"{thm}: {x}")
        other = sorted(other)
        errors = len(re.findall(r"\berror\b", out))
        ok = r.returncode == 0 and errors == 0 and not other and len(deps) + len(clean) == wanted
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {f.name}: theorems {len(deps) + len(clean)}/{wanted} "
              f"rc={r.returncode} errors={errors} other_axioms=[{', '.join(other)}]", flush=True)
        if not ok:
            print("\n".join("    " + l for l in out.splitlines()[:40]), flush=True)
    print(f"axiom audit: {len(files) - bad}/{len(files)} files ok")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
