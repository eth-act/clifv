#!/usr/bin/env python3
"""The verdict of a gate line whose exit status alone does not say that the check ran (#998).

usage: gate-line-check.py cargo-fv [--binary-check] COMPARE_LOG
       gate-line-check.py arm-fault-cosim LOG

Exit status 0 iff the log is that of a green line; prints one line: the lines the verdict was
read from, then `FAIL: <reason>` for every failed condition. The caller also requires the exit
status 0 of the gate's own command.

cargo-fv (the output of examples/compare.sh):
  - compare.sh's `SAME: N test outcomes identical` line with N > 0 and no `DIFFERENT …` line, and
  - with --binary-check: `cargo fv: binary check: N of N executable(s) verified` with N > 0 on
    every such line (docs/contracts/e2e.md, "Binary level (M9)"). `0 of N` (every executable
    "not checked", e.g. `link-check` not built), `N of M` with N < M, and no such line at all
    (no executable was checked) fail.

arm-fault-cosim (the output of scripts/arm-fault-cosim.sh):
  - exactly one line `TOTAL forms F vectors V faults X failures 0`, with F, V and X > 0: no form,
    no vector or no faulting vector means the memory-fault behaviour was not exercised.

Both gates call this script (.github/workflows/full-gate.yml and scripts/main-gate.sh), so they
cannot disagree on what a green line is.
"""
import re
import sys

SAME = re.compile(r"^SAME: (\d+) test outcomes identical")
BINARY = re.compile(r"^cargo fv: binary check: (\d+) of (\d+) executable\(s\) verified")
TOTAL = re.compile(r"^TOTAL forms (\d+) vectors (\d+) faults (\d+) failures (\d+)$")


def cargo_fv(text, binary_check):
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


def arm_fault_cosim(text):
    """(ok, one-line summary) for the text of an arm-fault-cosim log."""
    totals = [l for l in text.splitlines() if l.startswith("TOTAL")]
    fails = []
    if len(totals) != 1:
        fails.append(f"{len(totals)} TOTAL lines, want 1")
    for l in totals:
        m = TOTAL.match(l)
        if m is None:
            fails.append(f"unreadable TOTAL line: {l}")
            continue
        forms, vectors, faults, failures = (int(x) for x in m.groups())
        if failures:
            fails.append(f"{failures} failures")
        if not (forms and vectors and faults):
            fails.append(f"forms {forms}, vectors {vectors}, faults {faults}: want all above 0")
    return not fails, " ".join(totals + [f"FAIL: {f}" for f in fails])


def main(argv):
    kind, rest = (argv[0], argv[1:]) if argv else ("", [])
    args = [a for a in rest if a != "--binary-check"]
    binary_check = len(args) < len(rest)
    if kind not in ("cargo-fv", "arm-fault-cosim") or len(args) != 1 or args[0].startswith("-") \
            or (binary_check and kind != "cargo-fv"):
        print("\n".join(__doc__.strip().splitlines()[2:4]), file=sys.stderr)
        return 2
    try:
        with open(args[0], errors="replace") as f:
            text = f.read()
    except OSError as e:
        print(f"FAIL: {e}")
        return 1
    ok, line = cargo_fv(text, binary_check) if kind == "cargo-fv" else arm_fault_cosim(text)
    print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
