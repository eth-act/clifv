#!/usr/bin/env python3
"""Files that modules read while they elaborate, and the gate line that re-checks them (#1012).

usage: scripts/elab-inputs.py check [--log-dir DIR]   re-elaborate every reader from its source
       scripts/elab-inputs.py list                    module<TAB>source<TAB>inputs

Run `check` from the worktree root after the build, under scripts/memcap.sh like every Lean
command (`FV_MEMCAP=6G scripts/memcap.sh python3 scripts/elab-inputs.py check`; the readers
peak below 1 GB each).

Lake's trace of a module is its source, its imports, the toolchain and the Lake configuration.
A module that reads another file while it elaborates (an `#eval` check against a fixture) is
therefore not rebuilt when only that file changes: `lake build`, the shared Lake cache and the
CI baseline build all restore it, with the result of the check against the OLD file. Planning
the module (scripts/ci-build-plan.py) does not help by itself, for the same reason.

READERS lists those modules with the files each reads. Two things use it:

* `check` (a line of the full gate: .github/workflows/full-gate.yml, scripts/main-gate.sh) runs
  `lake lean SOURCE` on every reader: Lake restores the imports and Lean elaborates the source
  itself, whatever the cache holds for it, against the files of the checked-out tree. It runs on
  every gate run, not only when an input changed, so no baseline can carry a stale result.
* scripts/ci-build-plan.py plans the readers of a changed input, and their importers, like
  modules whose source changed (the plan shows them; `check` is what re-runs their checks).

scripts/test_elab_inputs.py fails when a module that may read a file while it elaborates
(`candidates`) is in neither READERS nor NOT_READERS: a new reader needs a row. `candidates` is
a heuristic over the source text, wide rather than exact; the weekly from-scratch run of the
full gate stays the check for an input nobody listed.
"""
import argparse, importlib.util, os, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent

# module -> the repository paths it reads while it elaborates (a trailing `/`: everything below).
# The Wasmtime sources (third_party/wasmtime, not tracked) change with their pin in
# scripts/fetch-third-party.sh.
READERS = {
    "FVTest.Isle.Interp": ["FVTest/Isle/oracle/cases.trace"],
    "FVTest.Isle.Opt": ["FVTest/Isle/oracle/opt.clif", "FVTest/Isle/oracle/opt.trace",
                        "FVTest/Isle/oracle/opt_skeleton.clif", "FVTest/Isle/oracle/opt_skeleton.trace"],
    # opt_corpus.trace names the corpus files that are read
    "FVTest.Isle.OptCorpus": ["FVTest/Isle/oracle/opt_corpus.trace", "corpus/clif/"],
    "FVTest.Isle.Pretty": ["scripts/fetch-third-party.sh"],
}
# module -> why it reads nothing while it elaborates, and the syntax it defines reads nothing
# where it is used, although `candidates` names it
NOT_READERS = {
    "FV.E2E.EmitEnc": "its elaborators (`destr`, `destr_all`, `cases_op`) are case splits in MetaM; the reading "
                      "call among its imports is FV.Backend.Regalloc's run-time call of lean-regalloc",
    "FV.E2E.LinkOwnFrames": "its elaborator `qs_priv%` builds the name of a constant; the reading call among "
                            "its imports is FV.Backend.Regalloc's run-time call of lean-regalloc",
}
WASMTIME = "third_party/wasmtime"
WASMTIME_READ = "cranelift/codegen"  # the part of the Wasmtime sources FVTest.Isle.Pretty reads

# calls that read a file, a directory or their metadata, the process environment or standard
# input, or start a process (which can read anything)
READS = re.compile(r"\b(readFile|readBinFile|readDir|walkDir|readToEnd|getLine)\b"
                   r"|\.(pathExists|isDir|metadata|realPath)\b|IO\.(getEnv|currentDir|appPath|getStdin)\b"
                   r"|IO\.FS\.(lines|Handle|withFile)|include_str|IO\.Process\.")
_MODIFIERS = r"(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|scoped|local|unsafe)\s+)*"
# commands and tactics that run code while their own module elaborates, or when it is imported
RUNS = re.compile(r"(?:^|[\s(])(#eval|run_cmd|run_elab|run_meta|run_tac)\b|^\s*" + _MODIFIERS
                  + r"(initialize|builtin_initialize)\b", re.M)
# definitions of elaborators: their code runs where they are used
ELABS = re.compile(r"^\s*" + _MODIFIERS + r"(elab|elab_rules)\b", re.M)
# definitions of syntax: what they expand or elaborate to runs where they are used
SYNTAX = re.compile(r"^\s*" + _MODIFIERS + r"(elab|elab_rules|macro|macro_rules|syntax|notation|infixl|infixr|infix"
                    r"|prefix|postfix)\b", re.M)


def load_lsb():
    spec = importlib.util.spec_from_file_location("lake_serial_build", ROOT / "scripts/lake-serial-build.py")
    lsb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lsb)
    return lsb


def code(text):
    """Lean source without comments (block comments do not nest here; a miss only adds a candidate)."""
    return re.sub(r"--.*", "", re.sub(r"/-.*?-/", "", text, flags=re.S))


def candidates(mods, imports, not_readers=()):
    """Modules that may read a file while they elaborate. A heuristic over the source text:

    * a command or tactic that runs code (`#eval`, `run_cmd`, `run_tac`, `initialize`, ...), or
      an elaborator definition, in a module whose imports, itself included, hold a reading call
      (the call may be a helper's in another module);
    * every module that imports such a module if that module also defines syntax (a macro that
      expands to `#eval check`, an elaborator that calls a reading helper: the code runs in the
      modules that use the syntax), unless it is in `not_readers`, which says the syntax it
      defines reads nothing.

    It cannot see a read behind `unsafe` code, a foreign function or an instance, nor which
    importer uses a syntax; and it names modules that only import a run-time reader (those go to
    NOT_READERS)."""
    text = {m: code(p.read_text(errors="replace")) for m, p in mods.items()}
    reads = {m for m, t in text.items() if READS.search(t)}

    def imports_a_read(m):
        seen, stack = set(), [m]
        while stack:
            x = stack.pop()
            if x in reads:
                return True
            if x not in seen:
                seen.add(x)
                stack.extend(imports[x])
        return False

    out = {m for m, t in text.items() if (RUNS.search(t) or ELABS.search(t)) and imports_a_read(m)}
    importers = {m: [] for m in mods}
    for m, deps in imports.items():
        for d in deps:
            importers[d].append(m)
    stack = [m for m in out if SYNTAX.search(text[m]) and m not in not_readers]
    spread = set()
    while stack:
        for r in importers[stack.pop()]:
            if r not in spread:
                spread.add(r)
                stack.append(r)
    return out | spread


def readers_of(files, readers=None):
    """Modules of READERS that read one of `files` (repository paths, e.g. a diff's names)."""
    readers = READERS if readers is None else readers
    return {m for m, inputs in readers.items()
            if any(f == i or (i.endswith("/") and f.startswith(i)) for f in files for i in inputs)}


def modified_sources(repo, subdir, run=subprocess.run):
    """Tracked files below `subdir` of the git checkout `repo` whose index or working tree
    differs from its HEAD (`git status --porcelain` lines), or None if git fails."""
    r = run(["git", "-C", str(repo), "status", "--porcelain", "--untracked-files=no", "--", subdir],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return None if r.returncode != 0 else [line for line in r.stdout.splitlines() if line.strip()]


def check(log_dir, run=subprocess.run):
    lsb = load_lsb()
    _, mods, _ = lsb.load_modules(ROOT)
    missing = sorted(m for m in READERS if m not in mods)
    if missing:
        print(f"elaboration-time inputs: no source for {' '.join(missing)}")
        return 1
    if log_dir:
        log_dir.mkdir(parents=True, exist_ok=True)
    # the pinned Wasmtime sources FVTest.Isle.Pretty reads: the script checks the commit, not
    # the files, and a checkout that lives across runs (scripts/main-gate.sh's worktree, a
    # checkout shared through a symbolic link) can hold edited files at the pinned commit
    fetch = run([str(ROOT / "scripts/fetch-third-party.sh"), "wasmtime"], cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if fetch.returncode != 0:
        print(f"elaboration-time inputs: scripts/fetch-third-party.sh wasmtime failed\n{fetch.stdout}")
        return 1
    edited = modified_sources(ROOT / WASMTIME, WASMTIME_READ, run)
    if edited is None or edited:
        print(f"elaboration-time inputs: {WASMTIME}/{WASMTIME_READ} is not the pinned commit's "
              + ("(git status failed)" if edited is None else f"({len(edited)} file(s) differ: {' | '.join(edited[:5])})"))
        return 1
    bad = []
    for m in sorted(READERS):
        source = os.path.relpath(mods[m], ROOT)
        start = time.time()
        # `lake lean`: the imports come from the build (or the cache), the file itself is
        # elaborated here and now; its checks read the working tree's files
        r = run(["lake", "lean", source], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if log_dir:
            (log_dir / f"{m}.log").write_text(r.stdout)
        ok = r.returncode == 0 and not re.search(r"^\S*:\d+:\d+: error", r.stdout, re.M)
        print(f"{'ok' if ok else 'FAIL'} {m} ({source}; reads {' '.join(READERS[m])}) {time.time() - start:.0f} s")
        if not ok:
            bad.append(m)
            print("\n".join(r.stdout.splitlines()[-30:]))
    print(f"elaboration-time inputs: {len(READERS) - len(bad)} of {len(READERS)} reading modules re-elaborated"
          + (f"; FAILED {' '.join(bad)}" if bad else ""))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    sub.add_parser("list")
    sub.add_parser("check").add_argument("--log-dir", type=pathlib.Path)
    a = ap.parse_args()
    if a.command == "check":
        return check(a.log_dir)
    _, mods, _ = load_lsb().load_modules(ROOT)
    for m in sorted(READERS):
        print(f"{m}\t{os.path.relpath(mods[m], ROOT) if m in mods else '?'}\t{' '.join(READERS[m])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
