#!/usr/bin/env python3
"""Axiom audit of the compiler theorems: run the `#print axioms` files in scripts/audit/ (or the
given files) through Lean and check that every listed theorem depends on no axiom other than
propext, Classical.choice and Quot.sound (docs/TO-PROVE.md §7, "Gate policy").

usage: scripts/axiom-audit.py [--log-dir DIR] [--cwd PKG] [FILE.lean...]

Run from the worktree root after the build (`lake build FV`): each file goes through
`lake env lean` in the worktree root, or in the Lake package PKG (relative to the root) with
`--cwd PKG` (`--cwd float-spec float-spec/audit.lean`: the FloatLib equality proofs, built by
scripts/float-spec.sh).

A command is a line `#print axioms X` outside comments and strings, X the theorem's full name (a
trailing `--` comment allowed). The line `#print axioms X -- witness: native_decide` (optionally
followed by ` (remark)`) marks a non-vacuity witness, which may also depend on the auxiliary axioms
`native_decide` adds (`Y._native.native_decide.ax_…`); compiler theorems may not.

The policy is decided twice, and both must pass (#1133):
- In Lean: the file runs as a copy in PKG/.lake/axiom-audit/: `import Lean`, the file's imports,
  LEAN_CHECK below, the command `#axiom_audit "<nonce>" "top" "<flags>" X₁ … Xₙ` (the commands'
  names in order, flag 1 for a witness), the rest of the file, and the same command with "end".
  The command compares every axiom of every Xₖ with the allowed names (by `Name`) and prints
  `axiom-audit <nonce> <phase> <k> 'Xₖ' native=<m>` per command (or `… <k> deferred` at the top
  for a theorem the file itself declares) and `axiom-audit <nonce> <phase> done <n>`. Each native
  axiom `Y._native.native_decide.ax_…` of a witness must be an axiom `e = true` for a closed Bool
  `e`, declared (by Lean's recorded range) inside declaration Y of the same module, as the
  `native_decide` in Y's proof that added it: one declared by hand (`axiom`, or a command macro)
  sits outside Y and fails. (Evaluating each `e` again instead took the audit from 6 to 74 minutes
  on main, 2026-11-19.) The top block runs before any code of the file and is the verdict for every
  theorem it resolves; both blocks must be complete, and the nonce is fresh per run, so no command
  of the file can print these lines unseen, and a file that stops early (`#exit`) fails.
- From the output: Lean prints one message per command, in command order:
  `'X' depends on axioms: [a, b, …]` (the list may wrap over several lines) or
  `'X' does not depend on any axioms`. The k-th message is the k-th command's result: its name
  must be the command's name and the number of messages the number of commands, so no result can
  be dropped, added or attributed to another command.
Not covered: Lean metaprograms written to deceive the audit (an elaborator that declares such an
axiom inside Y, code in a file that shadows what LEAN_CHECK calls for the end block); the audit
trusts the code it imports as it trusts the kernel check.

One line per file: results / commands, Lean errors, disallowed axioms in the printed lists, native
axioms checked, other problems. Exit status 0 iff every file compiles without an error (a file may
also check by other commands, e.g. a `run_cmd` that fails on an unexpected axiom), every command
has its own result and its own lines from LEAN_CHECK, and no disallowed axiom appears.
"""
import argparse, pathlib, re, secrets, subprocess, sys

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
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\\n'])'")
RAW = re.compile(r'r(#*)"')

# Inserted after the file's imports, before any of its code; full names only, no `open`. Names
# resolve as `#print axioms` resolves them (`realizeGlobalConstWithInfos`); `collectAxioms` is
# what it prints.
LEAN_CHECK = """
/-- scripts/axiom-audit.py: the axiom policy of the file's `#print axioms` commands. -/
elab "#axiom_audit " nonce:str phase:str flags:str ids:ident* : command => do
  let nonce := nonce.getString
  let phase := phase.getString
  let flags := flags.getString.toList.toArray
  unless flags.size == ids.size do
    throwError "axiom-audit: {flags.size} flags for {ids.size} names"
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let isNative : Lean.Name → Bool := fun ax => match ax.eraseMacroScopes with
    | .str (.str (.str _ "_native") "native_decide") s => s.startsWith "ax_"
    | _ => false
  let le : Lean.Position → Lean.Position → Bool := fun a b =>
    a.line < b.line || (a.line == b.line && a.column ≤ b.column)
  let mut done : Lean.NameSet := {}
  for i in [0:ids.size] do
    let witness := flags[i]! == '1'
    let cs ← try Lean.Elab.Command.liftCoreM (Lean.Elab.realizeGlobalConstWithInfos ids[i]!)
      catch ex => if phase == "top" then pure [] else throw ex
    if cs.isEmpty then
      Lean.logInfo m!"axiom-audit {nonce} {phase} {i} deferred"
    for c in cs do
      let mut n : Nat := 0
      for ax in ← Lean.collectAxioms c do
        if standard.contains ax then continue
        unless witness && isNative ax do
          Lean.logError m!"axiom-audit: '{c}' depends on the disallowed axiom {ax}"
          continue
        n := n + 1
        if done.contains ax then continue
        done := done.insert ax
        let env ← Lean.getEnv
        let some (.axiomInfo v) := env.find? ax
          | throwError "axiom-audit: native axiom {ax} is not an axiom"
        let some (ty, e, rhs) := v.type.eq?
          | throwError "axiom-audit: native axiom {ax} does not state `e = true`"
        unless ty.isConstOf ``Bool && rhs.isConstOf ``Bool.true && !e.hasFVar && !e.hasMVar do
          throwError "axiom-audit: native axiom {ax} does not state `e = true` for a closed Bool `e`"
        let y := ax.eraseMacroScopes.getPrefix.getPrefix.getPrefix
        let some r ← Lean.findDeclarationRanges? ax
          | throwError "axiom-audit: native axiom {ax} has no declaration range"
        let some ry ← Lean.findDeclarationRanges? y
          | throwError "axiom-audit: native axiom {ax}: {y} has no declaration range"
        unless env.getModuleIdxFor? ax == env.getModuleIdxFor? y && le ry.range.pos r.range.pos
            && le r.range.endPos ry.range.endPos do
          throwError "axiom-audit: native axiom {ax} is not declared inside {y}"
      Lean.logInfo m!"axiom-audit {nonce} {phase} {i} '{c}' native={n}"
  Lean.logInfo m!"axiom-audit {nonce} {phase} done {ids.size}"
"""


def ident_char(c):
    return c.isalnum() or c in "_'!?.»"


def strip_comments(text):
    """`text` with Lean comments (`--` to the end of the line, nested `/- … -/`), string, raw string
    and character literals blanked to spaces; newlines stay, so lines and columns are those of
    `text`."""
    out, i, n, depth = list(text), 0, len(text), 0

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        after_ident = i > 0 and ident_char(text[i - 1])
        if depth:
            step = 2 if text.startswith(("/-", "-/"), i) else 1
            depth += {"/-": 1, "-/": -1}.get(text[i:i + 2], 0) if step == 2 else 0
            blank(i, i + step)
            i += step
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
            blank(i, j + 1)
            i = j + 1
        elif not after_ident and (m := RAW.match(text, i)):
            j = text.find('"' + m.group(1), m.end())
            j = n if j < 0 else j + 1 + len(m.group(1))
            blank(i, j)
            i = j
        elif not after_ident and (m := CHAR.match(text, i)):
            blank(i, m.end())
            i = m.end()
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


def full_name(written):
    return written[len("_root_."):] if written.startswith("_root_.") else written


def check_source(text, nonce):
    """The copy of an audit file that Lean runs: `import Lean`, the file's imports, LEAN_CHECK and
    its top block, the rest of the file, the end block."""
    cmds = commands(text)[0]
    args = (f'"{"".join("1" if witness else "0" for _, witness in cmds)}"'
            + "".join(" " + name for name, _ in cmds))
    lines = text.split("\n")
    code = strip_comments(text).split("\n")
    head = next((k for k, c in enumerate(code) if c.strip() and not c.strip().startswith("import ")),
                len(lines))
    return "\n".join(["import Lean"] + lines[:head] + [LEAN_CHECK, f'#axiom_audit "{nonce}" "top" {args}']
                     + lines[head:] + [f'#axiom_audit "{nonce}" "end" {args}', ""])


def audit(text, out, rc, nonce):
    """Verdict on one file from its source `text`, the output `out` and exit code `rc` of Lean on
    `check_source(text, nonce)`. Returns (ok, summary, problems)."""
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
        if printed != full_name(written):
            problems.append(f"result {k + 1} names '{printed}', command {k + 1} names {written}")
        for x in axioms or []:
            if x not in STANDARD and not (witness and NATIVE.fullmatch(x)):
                other.append(f"{printed}: {x}")
    natives = [sum(bool(NATIVE.fullmatch(x)) for x in axioms or []) if witness else 0
               for (_, witness), (_, axioms) in zip(cmds, res)]
    want = [(str(k), full_name(written), str(m)) for k, ((written, _), m) in enumerate(zip(cmds, natives))]
    lines = re.findall(rf"^axiom-audit {nonce} (top|end) (?:(\d+) (?:'([^\n]*?)' native=(\d+)|deferred)|done (\d+))$",
                       out, re.M)
    if len(re.findall(nonce, out)) != len(lines):
        problems.append("a check message not at the start of a line")
    top = [l[1:4] for l in lines if l[0] == "top" and not l[4]]
    end = [l[1:4] for l in lines if l[0] == "end" and not l[4]]
    done = [(l[0], l[4]) for l in lines if l[4]]
    deferred = sum(1 for k, name, _ in top if not name)
    if (done != [("top", str(len(cmds))), ("end", str(len(cmds)))] or len(res) != len(cmds) or end != want
            or [t if t[1] else (t[0], *w[1:]) for t, w in zip(top, want)] != want or len(top) != len(want)):
        problems.append(f"Lean's checks top {top} end {end} done {done} for the commands {want}")
    errors = len(re.findall(r"\berror\b", out))
    ok = rc == 0 and errors == 0 and not other and not problems
    summary = (f"theorems {len(res)}/{len(cmds)} rc={rc} errors={errors} "
               f"other_axioms=[{', '.join(sorted(set(other)))}] native={sum(natives)}"
               + (f" checked_after_the_file={deferred}" if deferred else "")
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
    copies = cwd / ".lake" / "axiom-audit"
    copies.mkdir(parents=True, exist_ok=True)
    bad = 0
    for f in files:
        text = f.read_text()
        nonce = secrets.token_hex(16)
        run = copies / f.name
        run.write_text(check_source(text, nonce))
        r = subprocess.run(["lake", "env", "lean", str(run)], cwd=cwd, capture_output=True, text=True)
        out = r.stdout + r.stderr
        if a.log_dir:
            (pathlib.Path(a.log_dir) / f"{f.stem}.log").write_text(out)
        ok, summary, _ = audit(text, out, r.returncode, nonce)
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {f.name}: {summary}", flush=True)
        if not ok:
            print("\n".join("    " + l for l in out.splitlines()[:40]), flush=True)
    print(f"axiom audit: {len(files) - bad}/{len(files)} files ok")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
