#!/usr/bin/env python3
"""Axiom audit of the compiler theorems: run the `#print axioms` files in scripts/audit/ (or the
given files) through Lean and check that every listed theorem depends on no axiom other than
propext, Classical.choice and Quot.sound (docs/TO-PROVE.md §7, "Gate policy").

usage: scripts/axiom-audit.py [--log-dir DIR] [--cwd PKG] [FILE.lean...]

Run from the worktree root after the build (`lake build FV`): each file goes through
`lake env lean` in the worktree root, or in the Lake package PKG (relative to the root) with
`--cwd PKG` (`--cwd float-spec float-spec/audit.lean`: the FloatLib equality proofs, built by
scripts/float-spec.sh).

A command is a line `#print axioms X` (outside comments; a trailing `--` comment allowed). The
line `#print axioms X -- witness: native_decide` (optionally followed by ` (remark)`) marks a
non-vacuity witness, which may also depend on the auxiliary axioms `native_decide` adds
(`Y._native.native_decide.ax_…`); compiler theorems may not. The marked witnesses' auxiliary
axioms are re-evaluated in the same Lean run (a copy of the file with `import Lean` and the
command `#axiom_audit_native`, NATIVE_CHECK below, appended; it runs in DIR/.lake/axiom-audit/):
each must be an axiom `e = true` for a Bool `e` that the compiler evaluates to `true` now, as
`native_decide` did when it added it; an axiom declared by hand under such a name fails.

Lean prints one message per command, in command order: `'X' depends on axioms: [a, b, …]` (the
list may wrap over several lines) or `'X' does not depend on any axioms`. The k-th message is the
k-th command's result: its name must be the command's name (resolved: equal or a `.`-suffix), and
the number of messages must equal the number of commands, so no result can be dropped, added or
attributed to another command (#1133). One line per file: results / commands, Lean errors,
disallowed axioms, re-evaluated native axioms, other problems. Exit status 0 iff every file
compiles (a file may check by other commands only, e.g. a `run_cmd` that fails on an unexpected
axiom), every command has its own result, every native axiom of a witness re-evaluates to true,
and no disallowed axiom appears.
"""
import argparse, pathlib, re, subprocess, sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ROOT = pathlib.Path(__file__).resolve().parent.parent
# A trailing `✝` appears when the auxiliary native_decide axiom belongs to an inaccessible
# helper (e.g. a witness constant inside a namespace), as in `…observed_true._native.native_decide.ax_1✝`.
NATIVE = re.compile(r"[\w.'«»]+\._native\.native_decide\.ax_\w+✝?")
COMMAND = re.compile(r"[ \t]*#print[ \t]+axioms[ \t]+(\S+)[ \t]*")
ANY_COMMAND = re.compile(r"#print\s+axioms\b")
MARK = re.compile(r"--[ \t]*witness: native_decide(?:[ \t]+\(.*\))?[ \t]*")
RESULT = re.compile(r"^'([^\n]*?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M)
PHRASE = re.compile(r"depends on axioms|does not depend on any axioms")
CHECKED = re.compile(r"^axiom-audit native: '([^\n]*?)' (\d+) re-evaluated$", re.M)
CHECKED_ANY = re.compile(r"axiom-audit native:")

# Appended to a copy of a file with marked witnesses: for every witness (resolved like
# `#print axioms` resolves it) and every axiom of it named `…._native.native_decide.ax_…`, check that
# it is an axiom `e = true` for a Bool `e` and evaluate `e` again with `Lean.Meta.nativeEqTrue`, the
# function `native_decide` itself uses (in `withoutModifyingEnv`: the axiom it adds is dropped).
NATIVE_CHECK = """
open Lean Elab Command Meta in
/-- scripts/axiom-audit.py: re-evaluate the `native_decide` axioms of the marked witnesses. -/
elab "#axiom_audit_native" ids:ident* : command => do
  let isNative : Name → Bool := fun ax => match ax.eraseMacroScopes with
    | .str (.str (.str _ "_native") "native_decide") s => s.startsWith "ax_"
    | _ => false
  let mut done : NameSet := {}
  for id in ids do
    for c in ← liftCoreM (realizeGlobalConstWithInfos id) do
      let mut n : Nat := 0
      for ax in ← collectAxioms c do
        unless isNative ax do continue
        n := n + 1
        if done.contains ax then continue
        let some (.axiomInfo v) := (← getEnv).find? ax
          | throwError "axiom-audit: native axiom {ax} is not an axiom"
        let some (ty, e, rhs) := v.type.eq?
          | throwError "axiom-audit: native axiom {ax} does not state `e = true`"
        unless ty.isConstOf ``Bool && rhs.isConstOf ``Bool.true do
          throwError "axiom-audit: native axiom {ax} does not state `e = true` for a Bool `e`"
        match ← liftTermElabM (withoutModifyingEnv (nativeEqTrue `axiom_audit e)) with
        | .success _ => done := done.insert ax
        | .notTrue => throwError "axiom-audit: native axiom {ax} states `e = true` for an `e` that evaluates to false"
      logInfo m!"axiom-audit native: '{c}' {n} re-evaluated"
"""


def strip_comments(text):
    """`text` with Lean comments (`--` to the end of the line, nested `/- … -/`) and string literals
    blanked to spaces; newlines stay, so lines and columns are those of `text`."""
    out, i, n, depth = list(text), 0, len(text), 0

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1
                blank(i, i + 2)
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                blank(i, i + 2)
                i += 2
            else:
                blank(i, i + 1)
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            blank(i, i + 2)
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            blank(i, min(j + 1, n))
            i = j + 1
        else:
            i += 1
    return "".join(out)


def commands(text):
    """([(name, witness)] of the file's `#print axioms` commands in order, number of
    `#print axioms` occurrences outside comments and strings)."""
    code = strip_comments(text)
    cmds = []
    for code_line, line in zip(code.split("\n"), text.split("\n")):
        m = COMMAND.fullmatch(code_line)
        if m:
            cmds.append((m.group(1), bool(MARK.fullmatch(line[m.end(1):].strip()))))
    return cmds, len(ANY_COMMAND.findall(code))


def results(out):
    """[(name, axioms or None)] of Lean's `#print axioms` messages in order (None: no axioms)."""
    return [(m.group(1), None if m.group(2) is None else [x.strip() for x in m.group(2).split(",")])
            for m in RESULT.finditer(out)]


def names_match(printed, written):
    """`#print axioms written` may print `printed` (namespaces and `open` resolve `written`)."""
    if written.startswith("_root_."):
        written = written[len("_root_."):]
    return printed == written or printed.endswith("." + written)


def native_source(text, witnesses):
    """The copy of an audit file that also re-evaluates the native axioms of `witnesses`."""
    return ("import Lean\n" + text + ("" if text.endswith("\n") else "\n") + NATIVE_CHECK
            + "#axiom_audit_native " + " ".join(witnesses) + "\n")


def audit(text, out, rc, native_checked):
    """Verdict on one file from its source `text`, Lean's output `out` and exit code `rc`;
    `native_checked`: whether `out` comes from `native_source(text, …)` of its witnesses.
    Returns (ok, summary, problems)."""
    cmds, occurrences = commands(text)
    res = results(out)
    problems = []
    if occurrences != len(cmds):
        problems.append(f"{occurrences - len(cmds)} `#print axioms` not alone on its line")
    if len(PHRASE.findall(" ".join(out.split()))) != len(res):
        problems.append("a result message not at the start of a line")
    if len(res) != len(cmds):
        problems.append(f"{len(res)} results for {len(cmds)} commands")
    other = []
    for k, ((written, witness), (printed, axioms)) in enumerate(zip(cmds, res)):
        if not names_match(printed, written):
            problems.append(f"result {k + 1} names '{printed}', command {k + 1} names {written}")
        for x in axioms or []:
            if x not in STANDARD and not (witness and NATIVE.fullmatch(x)):
                other.append(f"{printed}: {x}")
    natives = [sum(bool(NATIVE.fullmatch(x)) for x in axioms or [])
               for (_, witness), (_, axioms) in zip(cmds, res) if witness]
    reevaluated = 0
    if native_checked:
        checked = CHECKED.findall(out)
        want = [printed for (_, witness), (printed, _) in zip(cmds, res) if witness]
        if len(CHECKED_ANY.findall(out)) != len(checked):
            problems.append("a native check message not at the start of a line")
        if [(p, int(n)) for p, n in checked] != list(zip(want, natives)):
            problems.append(f"native checks {checked} for witnesses {list(zip(want, natives))}")
        else:
            reevaluated = sum(natives)
    elif any(natives):
        problems.append("native axioms of witnesses not re-evaluated")
    errors = len(re.findall(r"\berror\b", out))
    ok = rc == 0 and errors == 0 and not other and not problems
    summary = (f"theorems {len(res)}/{len(cmds)} rc={rc} errors={errors} "
               f"other_axioms=[{', '.join(sorted(set(other)))}] native_reevaluated={reevaluated}"
               + (f" problems=[{'; '.join(problems)}]" if problems else ""))
    return ok, summary, problems


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("files", nargs="*")
    ap.add_argument("--log-dir", help="write each file's Lean output to DIR/<name>.log")
    ap.add_argument("--cwd", default=".", help="Lake package to run `lake env lean` in")
    a = ap.parse_args()
    cwd = ROOT / a.cwd
    files = [pathlib.Path(f).resolve() for f in a.files] or sorted((ROOT / "scripts/audit").glob("*.lean"))
    if not files:
        print("axiom audit: no files")
        return 1
    if a.log_dir:
        pathlib.Path(a.log_dir).mkdir(parents=True, exist_ok=True)
    bad = 0
    for f in files:
        text = f.read_text()
        witnesses = [name for name, witness in commands(text)[0] if witness]
        run = f
        if witnesses:
            run = cwd / ".lake" / "axiom-audit" / f.name
            run.parent.mkdir(parents=True, exist_ok=True)
            run.write_text(native_source(text, witnesses))
        r = subprocess.run(["lake", "env", "lean", str(run)], cwd=cwd, capture_output=True, text=True)
        out = r.stdout + r.stderr
        if a.log_dir:
            (pathlib.Path(a.log_dir) / f"{f.stem}.log").write_text(out)
        ok, summary, _ = audit(text, out, r.returncode, bool(witnesses))
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {f.name}: {summary}", flush=True)
        if not ok:
            print("\n".join("    " + l for l in out.splitlines()[:40]), flush=True)
    print(f"axiom audit: {len(files) - bad}/{len(files)} files ok")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
