#!/usr/bin/env python3
"""The verdict of a gate line whose exit status alone does not say that the check ran (#998).

usage: gate-line-check.py cargo-fv EXAMPLE [--lean-link] [--known FILE] [--expected FILE] [--base FILE] [--summary FILE] COMPARE_LOG FV_LOG
       gate-line-check.py base-pins OUT (--before SHA | --local REV)
       gate-line-check.py arm-fault-cosim LOG

Exit status 0 iff the log is that of a green line; prints one line: the lines the verdict was
read from, then `FAIL: <reason>` for every failed condition. The caller also requires the exit
status 0 of the gate's own command.

cargo-fv (EXAMPLE: the directory name under examples/; COMPARE_LOG: the output of
examples/compare.sh; FV_LOG: cargo fv's own output, the fv.log in the directory compare.sh names
in its `(logs: DIR)`):
  - compare.sh's `SAME: N test outcomes identical` line with N > 0 and no `DIFFERENT …` line, and
  - exactly one line `cargo fv: N of M functions compiled by the Lean backend (V verified)` with
    N > 0 (identical outcomes prove nothing about the Lean backend if every function kept
    cg_clif's code), and
  - no line of cargo fv or fv-rustc in FV_LOG that reports a missing tool or a fallback: `cannot
    run`, `missing`, `not checked`, `linking with rust-lld` (cargo fv treats a missing `lean-ld`
    or `link-check` as a warning: the gate ran for weeks on rust-lld with every executable "not
    checked", #998, #1004), and
  - the binary check (docs/contracts/e2e.md, "Binary level (M9)"), on every line: exactly one
    line `cargo fv: binary check: N of M executable(s) verified` with M > 0 that agrees with the
    per-executable lines (`cargo fv: binary PATH: verified: …` / `not verified: …` /
    `not checked: …`), and the executables that are not verified are EXACTLY the entries of
    EXAMPLE in the known-unverified list (--known FILE, default gate-known-unverified.txt beside
    this script). No entry: N of N. `0 of N` without an entry and no count line at all fail
    (#1008: bigframe-unwind's `0 of 1` passed without a word). An executable that stops
    verifying fails, and so does a listed one that verifies again ("remove the entry"), so the
    list cannot go stale: the PR that fixes an entry's issue deletes the entry. An executable is
    named `<package>/<file without its -<hash> suffix>`, from PATH
    `…/build/<package>/<hash>/out/<file>`; and
  - the pinned counts of EXAMPLE (--expected FILE, default gate-expected-counts.txt beside this
    script: `EXAMPLE  EXECUTABLES  LEAN  VERIFIED`): the M of the binary check line equals
    EXECUTABLES; the N and the V of the functions line are not below LEAN and VERIFIED (a drop
    is a regression) and not above them either: a rise is recorded by changing the file in the
    same PR (the verdict prints the new line). Without the pins `N of N` passed with a smaller N:
    a crate whose codegen units all fall back to cg_clif leaves the executable count (#1004).
    With --base FILE (the expected counts of the base revision: main's copy, which the CI gate
    fetches) no pin of EXAMPLE is below the base revision's: a PR records rises, it cannot make
    a drop green by lowering the pin in the same change (LEARNINGS.md, "Untrusted input never
    widens the policy"); a deliberate drop is a parent decision, merged with this line red;
  - with --lean-link (the lines that link with lean-ld): at least one `linked by lean-ld` line
    and no `linked by rust-lld` line in FV_LOG.
  --summary FILE appends the counts (pinned and measured) and the known-unverified executables
  with cargo fv's reasons to FILE as Markdown (the CI job summary).

base-pins (run in the checkout): writes to OUT the expected counts of the base revision of this
run, for `cargo-fv --base OUT`, and prints the revision. The base revision is never the tested
commit. OUT is empty when the base revision has no such file; exit status 1 and no OUT when the
revision cannot be found (`cargo-fv --base OUT` then fails: no base, no green line).
  --before SHA (CI; SHA: the push event's `before`, or empty): on a branch main's tip; on main
    the tip the push replaced, or the tested commit's parent when there is none (a re-run, the
    weekly run). Fetched from origin. Read from the environment: GITHUB_REF, GITHUB_EVENT_NAME,
    GITHUB_SHA.
  --local REV (scripts/main-gate.sh; nothing is fetched): REV, the loop's last green commit; with
    an empty REV (a one-shot run) the commit where HEAD left origin/main, or HEAD's parent when
    HEAD is on origin/main.

arm-fault-cosim (the output of scripts/arm-fault-cosim.sh):
  - exactly one line `TOTAL forms F vectors V faults X failures 0`, with F, V and X > 0: no form,
    no vector or no faulting vector means the memory-fault behaviour was not exercised.

Both gates call this script (.github/workflows/full-gate.yml and scripts/main-gate.sh), so they
cannot disagree on what a green line is.
"""
import collections
import os
import pathlib
import re
import subprocess
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
HERE = pathlib.Path(__file__).resolve().parent
KNOWN = HERE / "gate-known-unverified.txt"
EXPECTED = HERE / "gate-expected-counts.txt"
# the pinned counts, in the file's column order
PINS = ("executables through the binary check", "functions compiled by the Lean backend", "verified functions")


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


def read_expected(text, example):
    """(the pinned (executables, Lean-compiled, verified) of `example` or None, errors) from the
    text of the expected counts: `EXAMPLE  EXECUTABLES  LEAN  VERIFIED` lines, `#` comments, one
    line per example."""
    pinned, errors, seen = None, [], set()
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        w = line.split()
        if len(w) != 4 or not all(re.fullmatch(r"\d+", x) for x in w[1:]) or int(w[3]) > int(w[2]):
            errors.append(f"unreadable expected-counts line: {line.strip()}")
        elif w[0] in seen:
            errors.append(f"two expected-counts lines for {w[0]}")
        else:
            seen.add(w[0])
            if w[0] == example:
                pinned = tuple(int(x) for x in w[1:])
    return pinned, errors


def exe_name(path):
    m = EXE_PATH.search(path)
    return f"{m[1]}/{m[2]}" if m else path


def measured(lines):
    """The counts of a compare.sh log, in the order of PINS; None where the log does not have
    exactly one readable line for the count."""
    counts = [m for m in map(COUNT.match, lines) if m]
    funcs = [m for m in map(FUNCS.match, lines) if m]
    exes = int(counts[0][2]) if len(counts) == 1 else None
    lean, verified = (int(funcs[0][1]), int(funcs[0][3])) if len(funcs) == 1 else (None, None)
    return exes, lean, verified


def pin_fails(example, got, pinned):
    """The failed conditions of the pinned counts. A count the log lacks (None) fails its own
    condition elsewhere."""
    if pinned is None:
        return [f"no pinned counts for {example} (scripts/gate-expected-counts.txt)"]
    new = "  ".join([example] + [str(p if g is None else g) for g, p in zip(got, pinned)])
    fails = []
    for i, (what, g, p) in enumerate(zip(PINS, got, pinned)):
        if g is None or g == p:
            continue
        if i == 0:
            fails.append(f"{what}: {g}, pinned {p} (exact; an intended change sets `{new}` in "
                         "scripts/gate-expected-counts.txt in the same PR)")
        elif g < p:
            fails.append(f"{what}: {g} is below the pinned {p} (a regression)")
        else:
            fails.append(f"{what}: {g} is above the pinned {p}: record the rise in the same PR "
                         f"(`{new}` in scripts/gate-expected-counts.txt)")
    return fails


def base_fails(pinned, base):
    """The failed conditions of the pins against the base revision's pins of the example (None:
    it has none, e.g. a new example)."""
    if pinned is None or base is None:
        return []
    return [f"pinned {what}: {p} is below the base revision's {b} (scripts/gate-expected-counts.txt on main): "
            "a PR may raise a pin, lowering one is a parent decision"
            for what, p, b in zip(PINS, pinned, base) if p < b]


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


def cargo_fv(example, text, lean_link, known=(), fv_log="", pinned=None, base=None):
    """(ok, one-line summary) for the text of a compare.sh log and of cargo fv's own log;
    `lean_link`: a --lean-link line; `known`: the known-unverified entries [(executable, issue)]
    of the example; `pinned`: its expected (executables, Lean-compiled, verified) counts; `base`:
    the base revision's (None: not compared)."""
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
    fails += fallback_fails(fv_log, lean_link)
    fails += binary_fails(lines, list(known))
    fails += pin_fails(example, measured(lines), pinned)
    fails += base_fails(pinned, base)
    shown = [l for l in lines if l.startswith("cargo fv: binary check:")] + same + different
    shown += [m[0].removeprefix("cargo fv: ") for m in funcs]
    if pinned is not None:
        shown.append("pinned (scripts/gate-expected-counts.txt): "
                     + ", ".join(f"{p} {w}" for p, w in zip(pinned, ("executables", "Lean-compiled", "verified"))))
    if known:
        shown.append("known unverified (scripts/gate-known-unverified.txt): "
                     + ", ".join(f"{e} {i}" for e, i in known))
    return not fails, " ".join(shown + [f"FAIL: {f}" for f in fails])


def summary(example, text, known, pinned, env=os.environ, base=None):
    """Markdown for the CI job summary: the pinned and the measured counts of the line, and the
    known-unverified executables with their issue and cargo fv's reason; `base`: the base
    revision's pins, named when they differ."""
    lines = text.splitlines()
    got = measured(lines)
    out = [f"### cargo fv counts: {example}", "",
           "| | pinned (`scripts/gate-expected-counts.txt`) | this run | |", "|---|---:|---:|---|"]
    for i, what in enumerate(PINS):
        p, g = (None if pinned is None else pinned[i]), got[i]
        if p is None or g is None:
            note = "**missing**"
        elif g == p:
            note = "equal"
        elif i == 0:
            note = f"**{g - p:+d}: must be equal**"
        else:
            note = f"**{g - p:+d}: a regression**" if g < p else f"**{g - p:+d}: record the rise in this PR**"
        out.append(f"| {what} | {'none' if p is None else p} | {'none' if g is None else g} | {note} |")
    out += ["", "The executables must be equal. A function count below its pin is a regression; one above it is "
            "recorded by changing the file in the same PR."]
    if None not in got and pinned is not None and got != pinned:
        out += ["", "This run's line: `" + "  ".join([example] + [str(g) for g in got]) + "`"]
    if base is not None and pinned is not None and base != pinned:
        out += ["", "The base revision (main) pins `" + "  ".join([example] + [str(b) for b in base]) + "`"
                + ("; **a pin below it is red**: a PR may raise a pin, lowering one is a parent decision."
                   if base_fails(pinned, base) else "; no pin of this branch is below it.")]
    if known:
        repo = env.get("GITHUB_SERVER_URL", ""), env.get("GITHUB_REPOSITORY", "")
        why = collections.defaultdict(list)
        for m in filter(None, map(EXE.match, lines)):
            if not m[2].startswith("verified: "):
                why[exe_name(m[1])].append(m[2])
        out += ["", f"### Known unverified executables: {example}", "",
                "The line is green only while exactly these executables fail the binary check "
                "(`scripts/gate-known-unverified.txt`): one more is red, and so is one fewer (the PR that "
                "fixes an entry removes it).", ""]
        for e, issue in known:
            link = f"{repo[0]}/{repo[1]}/issues/{issue[1:]}" if all(repo) else issue
            reasons = why[e] or ["(no `not verified` line in this run)"]
            out.append(f"- `{e}`: {link}: {reasons.pop(0)[:600]}")
    return "\n".join(out) + "\n\n"


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


def base_revision(ref, event, before, sha):
    """(what to fetch from origin, depth, the commit among the fetched) for the base revision of
    a CI run on `ref` at commit `sha`: never the tested commit itself (a push run on main that
    read main's tip compared the pins with themselves)."""
    if ref != "refs/heads/main":
        return "main", 1, "FETCH_HEAD"
    if event == "push" and re.fullmatch(r"[0-9a-f]{40}", before or "") and set(before) != {"0"}:
        return before, 1, "FETCH_HEAD"
    return sha, 2, "FETCH_HEAD^"


def local_base_revision(rev, git):
    """The base revision of a local run: `rev` (scripts/main-gate.sh's last green commit) when
    given; else, for a one-shot run, the commit where HEAD left origin/main (a branch), or
    HEAD's parent when HEAD is on origin/main (main itself, a bisection). None: unknown."""
    if rev:
        return rev
    head, fork = git("rev-parse", "HEAD"), git("merge-base", "HEAD", "origin/main")
    if head.returncode != 0 or fork.returncode != 0:
        return None
    return "HEAD^" if fork.stdout.strip() == head.stdout.strip() else fork.stdout.strip()


def base_pins(out, mode, value, env=os.environ):
    """Write the base revision's expected counts to `out`; the exit status. `mode`: `--before`
    (CI: `value` is the push event's `before`) or `--local` (`value`: the last green commit)."""
    path = pathlib.Path(out)
    path.unlink(missing_ok=True)
    git = lambda *a: subprocess.run(["git", *a], capture_output=True, text=True)
    if mode == "--before":
        what, depth, rev = base_revision(env.get("GITHUB_REF", ""), env.get("GITHUB_EVENT_NAME", ""), value,
                                         env.get("GITHUB_SHA", ""))
        r = git("fetch", "-q", "--depth", str(depth), "origin", what)
    else:
        what, rev = "local", local_base_revision(value, git)
        r = subprocess.CompletedProcess([], 0 if rev else 1, "", "HEAD or origin/main is unknown")
    commit = git("rev-parse", "-q", "--verify", f"{rev}^{{commit}}") if r.returncode == 0 else r
    if commit.returncode != 0:
        print(f"FAIL: base revision {what} ({rev}): {(r.stderr or commit.stderr).strip() or 'not found'}")
        return 1
    name = f"{commit.stdout.strip()}:scripts/gate-expected-counts.txt"
    text = ""
    if git("cat-file", "-e", name).returncode == 0:
        shown = git("show", name)
        if shown.returncode != 0:
            print(f"FAIL: base revision: git show {name}: {shown.stderr.strip()}")
            return 1
        text = shown.stdout
    path.write_text(text)
    print(f"base revision {commit.stdout.strip()[:9]} ({what}, {rev}): "
          + (f"{sum(1 for l in text.splitlines() if l.strip() and not l.lstrip().startswith('#'))} pinned line(s)"
             if text else "no scripts/gate-expected-counts.txt"))
    return 0


def usage():
    print("\n".join(__doc__.strip().splitlines()[2:5]), file=sys.stderr)
    return 2


def main(argv):
    if argv and argv[0] == "base-pins":
        if len(argv) == 4 and argv[2] in ("--before", "--local") and argv[1].strip() and not argv[1].startswith("-"):
            return base_pins(argv[1], argv[2], argv[3])
        return usage()
    if not argv or argv[0] not in ("cargo-fv", "arm-fault-cosim"):
        return usage()
    kind, rest = argv[0], argv[1:]
    opts, args = {}, []
    while rest:
        a = rest.pop(0)
        if a in ("--known", "--expected", "--base", "--summary") and kind == "cargo-fv" and rest and a not in opts:
            opts[a] = rest.pop(0)
        elif a == "--lean-link" and kind == "cargo-fv" and a not in opts:
            opts[a] = True
        elif a.startswith("-"):
            return usage()
        else:
            args.append(a)
    if len(args) != (3 if kind == "cargo-fv" else 1) or not all(a.strip() for a in args):
        return usage()
    try:
        with open(args[1] if kind == "cargo-fv" else args[0], errors="replace") as f:
            text = f.read()
        if kind == "arm-fault-cosim":
            ok, line = arm_fault_cosim(text)
        else:
            example = args[0]
            with open(args[2], errors="replace") as f:
                fv_log = f.read()
            known, errors = read_known(pathlib.Path(opts.get("--known", KNOWN)).read_text(), example)
            pinned, errors2 = read_expected(pathlib.Path(opts.get("--expected", EXPECTED)).read_text(), example)
            base, errors3 = (None, [])
            if "--base" in opts:
                base, errors3 = read_expected(pathlib.Path(opts["--base"]).read_text(), example)
                errors3 = [f"base revision: {e}" for e in errors3]
            ok, line = cargo_fv(example, text, "--lean-link" in opts, known, fv_log, pinned, base)
            if errors + errors2 + errors3:
                ok, line = False, " ".join([line] + [f"FAIL: {e}" for e in errors + errors2 + errors3])
            if "--summary" in opts:
                with open(opts["--summary"], "a") as f:
                    f.write(summary(example, text, known, pinned, base=base))
    except OSError as e:
        print(f"FAIL: {e}")
        return 1
    print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
