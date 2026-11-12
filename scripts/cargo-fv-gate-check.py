#!/usr/bin/env python3
"""The verdict of a `cargo fv` gate line, from the output of examples/compare.sh (#998).

usage: cargo-fv-gate-check.py [--binary-check] COMPARE_LOG

Exit status 0 iff the log
  - has compare.sh's `SAME: N test outcomes identical` line with N > 0 and no `DIFFERENT …` line,
    and
  - with --binary-check: has `cargo fv: binary check: N of N executable(s) verified` with N > 0
    on every such line (docs/contracts/e2e.md, "Binary level (M9)"). `0 of N` (every executable
    "not checked", e.g. `link-check` not built), `N of M` with N < M, and no such line at all
    (no executable was checked) fail.
Prints one line: the lines the verdict was read from, then `FAIL: <reason>` for every failed
condition. The caller also requires compare.sh's exit status 0.

Both gates call this script (.github/workflows/full-gate.yml and scripts/main-gate.sh), so they
cannot disagree on what a green `cargo fv` line is.
"""
import re
import sys

SAME = re.compile(r"^SAME: (\d+) test outcomes identical")
BINARY = re.compile(r"^cargo fv: binary check: (\d+) of (\d+) executable\(s\) verified")


def verdict(text, binary_check):
    """(ok, one-line summary) for the text of a compare.sh log."""
    lines = text.splitlines()
    same = [l for l in lines if l.startswith("SAME")]
    different = [l for l in lines if l.startswith("DIFFERENT")]
    binary = [(l, BINARY.match(l)) for l in lines if l.startswith("cargo fv: binary check:")]
    fails = []
    if not same:
        fails.append("no SAME line")
    for l in same:
        m = SAME.match(l)
        if m is None or int(m[1]) == 0:
            fails.append(f"SAME line without test outcomes: {l}")
    if different:
        fails.append("DIFFERENT line")
    if binary_check:
        if not binary:
            fails.append("no `binary check:` line (no executable went through the binary check)")
        for l, m in binary:
            if m is None:
                fails.append(f"unreadable binary check line: {l}")
            elif int(m[1]) != int(m[2]) or int(m[2]) == 0:
                fails.append(f"binary check: {m[1]} of {m[2]} executable(s) verified, want all (and at least one)")
    shown = [l for l, _ in binary] + same + different + [f"FAIL: {f}" for f in fails]
    return not fails, " ".join(shown)


def main(argv):
    args = [a for a in argv if a != "--binary-check"]
    if len(args) != 1 or args[0].startswith("-"):
        print(__doc__.strip().splitlines()[2], file=sys.stderr)
        return 2
    try:
        with open(args[0], errors="replace") as f:
            text = f.read()
    except OSError as e:
        print(f"FAIL: {e}")
        return 1
    ok, line = verdict(text, "--binary-check" in argv)
    print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
