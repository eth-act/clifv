#!/usr/bin/env python3
"""The verdict of a gate line whose exit status alone does not say that the check ran (#998).

usage: gate-line-check.py cargo-fv [--binary-check EXAMPLE] [--known FILE] COMPARE_LOG FV_LOG
       gate-line-check.py arm-fault-cosim LOG

Exit status 0 iff the log is that of a green line; prints one line: the lines the verdict was
read from, then `FAIL: <reason>` for every failed condition. The caller also requires the exit
status 0 of the gate's own command.

cargo-fv (COMPARE_LOG: the output of examples/compare.sh; FV_LOG: cargo fv's own output, the
fv.log in the directory compare.sh names in its `(logs: DIR)`):
  - compare.sh's `SAME: N test outcomes identical` line with N > 0 and no `DIFFERENT …` line, and
  - exactly one line `cargo fv: N of M functions compiled by the Lean backend (V verified)` with
    N > 0 (identical outcomes prove nothing about the Lean backend if every function kept
    cg_clif's code; the counts are shown in the verdict line), and
  - no line of cargo fv or fv-rustc in FV_LOG that reports a missing tool or a fallback: `cannot
    run`, `missing`, `not checked`, `linking with rust-lld` (cargo fv treats a missing `lean-ld`
    or `link-check` as a warning: the gate ran for weeks on rust-lld with every executable "not
    checked", #998, #1004), and
  - with --binary-check EXAMPLE (docs/contracts/e2e.md, "Binary level (M9)"): exactly one line
    `cargo fv: binary check: N of M executable(s) verified` with M > 0 that agrees with the
    per-executable lines (`cargo fv: binary PATH: verified: …` / `not verified: …` /
    `not checked: …`), and the executables that are not verified are EXACTLY the entries of
    EXAMPLE in the known-unverified list (FILE, default gate-known-unverified.txt beside this
    script). No entry (every example but the listed ones): N of N. `0 of N` (every executable
    "not checked", e.g. `link-check` not built) and no count line at all fail. An executable
    that stops verifying fails, and so does a listed one that verifies again ("remove the
    entry"), so the list cannot go stale: the PR that fixes an entry's issue deletes the entry.
    An executable is named `<package>/<file without its -<hash> suffix>`, from PATH
    `…/build/<package>/<hash>/out/<file>`. Also (the --lean-link lines link with lean-ld): at
    least one `linked by lean-ld` line and no `linked by rust-lld` line in FV_LOG.

arm-fault-cosim (the output of scripts/arm-fault-cosim.sh):
  - exactly one line `TOTAL forms F vectors V faults X failures 0`, with F, V and X > 0: no form,
    no vector or no faulting vector means the memory-fault behaviour was not exercised.

Both gates call this script (.github/workflows/full-gate.yml and scripts/main-gate.sh), so they
cannot disagree on what a green line is.
"""
import collections
import pathlib
import re
import sys

SAME = re.compile(r"^SAME: (\d+) test outcomes identical")
COUNT = re.compile(r"^cargo fv: binary check: (\d+) of (\d+) executable\(s\) verified")
FUNCS = re.compile(r"^cargo fv: (\d+) of (\d+) functions compiled by the Lean backend \((\d+) verified\)")
EXE = re.compile(r"^cargo fv: binary (/\S+): (.*)$")
EXE_PATH = re.compile(r"/build/([^/]+)/[0-9a-f]+/out/([^/]+?)(?:-[0-9a-f]{16})?$")
TOTAL = re.compile(r"^TOTAL forms (\d+) vectors (\d+) faults (\d+) failures (\d+)$")
# cargo fv's and fv-rustc's own lines (not the compiled crates' or the tests' output) that
# report a tool it could not run or a fallback it took
FV_LINE = re.compile(r"^\s*cargo fv\b|\bfv-rustc: ")
FALLBACK = re.compile(r"cannot run|\bmissing\b|not checked|linking with rust-lld")
KNOWN = pathlib.Path(__file__).resolve().parent / "gate-known-unverified.txt"


def read_known(text, example):
    """(entries of `example` as [(executable, issue)], errors) from the text of the list:
    `EXAMPLE  PACKAGE/EXECUTABLE  #ISSUE` lines, `#` comments. A line repeated twice names two
    executables (a package can link several with one name)."""
    entries, errors = [], []
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        w = line.split()
        if len(w) != 3 or "/" not in w[1] or not re.fullmatch(r"#\d+", w[2]):
            errors.append(f"unreadable known-unverified line: {line.strip()}")
        elif w[0] == example:
            entries.append((w[1], w[2]))
    return entries, errors


def exe_name(path):
    m = EXE_PATH.search(path)
    return f"{m[1]}/{m[2]}" if m else path


def binary_fails(lines, known):
    """The failed conditions of the binary check, for the known-unverified entries `known`."""
    counts = [(l, COUNT.match(l)) for l in lines if l.startswith("cargo fv: binary check:")]
    if len(counts) != 1:
        return [f"{len(counts)} `binary check:` lines, want 1 (none: no executable went through the binary check)"]
    line, m = counts[0]
    if m is None:
        return [f"unreadable binary check line: {line}"]
    exes = [m2 for m2 in map(EXE.match, lines) if m2]
    unverified = [exe_name(m2[1]) for m2 in exes if not m2[2].startswith("verified: ")]
    fails = []
    if int(m[2]) == 0:
        fails.append("binary check: no executable")
    if int(m[2]) != len(exes) or int(m[1]) != len(exes) - len(unverified):
        fails.append(f"binary check: {m[1]} of {m[2]} disagrees with the per-executable lines "
                     f"({len(exes) - len(unverified)} of {len(exes)} verified)")
    got, want = collections.Counter(unverified), collections.Counter(e for e, _ in known)
    issue = dict(known)
    for e, n in sorted((got - want).items()):
        fails.append(f"not verified: {e}" + (f" (x{n})" if n > 1 else "")
                     + (f" (more than the known list's, {issue[e]})" if e in issue else ""))
    for e, n in sorted((want - got).items()):
        fails.append(f"{e} is in the known-unverified list ({issue[e]}) but is verified or absent: remove the entry"
                     + (f" (x{n})" if n > 1 else ""))
    return fails


def fallback_fails(fv_log, lean_ld):
    """The failed conditions on cargo fv's own log; `lean_ld`: the line links with lean-ld."""
    own = [l.strip() for l in fv_log.splitlines() if FV_LINE.search(l)]
    fails = [f"fallback or missing tool: {l[:300]}" for l in dict.fromkeys(own) if FALLBACK.search(l)]
    if lean_ld:
        rust_lld = sum("linked by rust-lld" in l for l in own)
        if rust_lld:
            fails.append(f"{rust_lld} link(s) by rust-lld, want lean-ld")
        if not any("linked by lean-ld" in l for l in own):
            fails.append("no `linked by lean-ld` line")
    return fails


def cargo_fv(text, binary_check, known=(), fv_log=""):
    """(ok, one-line summary) for the text of a compare.sh log and of cargo fv's own log;
    `known`: the known-unverified entries [(executable, issue)] of the example (used with
    binary_check)."""
    lines = text.splitlines()
    same = [l for l in lines if l.startswith("SAME")]
    different = [l for l in lines if l.startswith("DIFFERENT")]
    fails = []
    if len(same) != 1:
        fails.append(f"{len(same)} SAME lines, want 1")
    for l in same:
        m = SAME.match(l)
        if m is None or int(m[1]) == 0:
            fails.append(f"SAME line without test outcomes: {l}")
    if different:
        fails.append("DIFFERENT line")
    funcs = [m for m in map(FUNCS.match, lines) if m]
    if len(funcs) != 1:
        fails.append(f"{len(funcs)} `functions compiled by the Lean backend` lines, want 1")
    elif int(funcs[0][1]) == 0:
        fails.append("no function compiled by the Lean backend")
    fails += fallback_fails(fv_log, binary_check)
    shown = [l for l in lines if l.startswith("cargo fv: binary check:")] + same + different
    shown += [m[0].removeprefix("cargo fv: ") for m in funcs]
    if binary_check:
        fails += binary_fails(lines, list(known))
        if known:
            shown.append("known unverified (scripts/gate-known-unverified.txt): "
                         + ", ".join(f"{e} {i}" for e, i in known))
    return not fails, " ".join(shown + [f"FAIL: {f}" for f in fails])


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


def usage():
    print("\n".join(__doc__.strip().splitlines()[2:4]), file=sys.stderr)
    return 2


def main(argv):
    if not argv or argv[0] not in ("cargo-fv", "arm-fault-cosim"):
        return usage()
    kind, rest = argv[0], argv[1:]
    opts, args = {}, []
    while rest:
        a = rest.pop(0)
        if a in ("--binary-check", "--known") and kind == "cargo-fv" and rest and a not in opts:
            opts[a] = rest.pop(0)
        elif a.startswith("-"):
            return usage()
        else:
            args.append(a)
    example = opts.get("--binary-check")
    if len(args) != (2 if kind == "cargo-fv" else 1) or (example is None and "--known" in opts) \
            or (example is not None and not example.strip()):
        return usage()
    try:
        with open(args[0], errors="replace") as f:
            text = f.read()
        known, errors, fv_log = [], [], ""
        if kind == "cargo-fv":
            with open(args[1], errors="replace") as f:
                fv_log = f.read()
        if example is not None:
            path = pathlib.Path(opts.get("--known", KNOWN))
            known, errors = read_known(path.read_text(), example)
    except OSError as e:
        print(f"FAIL: {e}")
        return 1
    if kind == "arm-fault-cosim":
        ok, line = arm_fault_cosim(text)
    else:
        ok, line = cargo_fv(text, example is not None, known, fv_log)
        if errors:
            ok, line = False, " ".join([line] + [f"FAIL: {e}" for e in errors])
    print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
