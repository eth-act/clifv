#!/usr/bin/env python3
"""Port the Lean sources to the module system, scripted so the port can be regenerated on any main.

usage: scripts/module-port.py [--check] [FILE_OR_DIR...]   (default: FV FVTest corpus/dsl/Corpus)
       scripts/module-port.py regen OLD_MAIN OLD_PORT       (run on a checkout of the new main)
       scripts/module-port.py unexpose [--only MODLIST]
       scripts/module-port.py privatize [--report FILE] [--only MODLIST] MODULE...   (built tree)

Mechanical step (default): each file that does not start with `module` gets
  * `module` before its first import (after leading comments),
  * `public import M` for every `import M`,
  * `@[expose] public section` after the imports: every declaration stays public and every
    definition body stays unfoldable by importers, as before the port; theorem proofs become
    private, so a proof-only edit no longer changes the module's public interface.
Files already starting with `module` are left alone. --check lists the files that are not ported
and exits 1 if there are any.

regen: the fix-ups the mechanical step cannot do (`meta` on elaboration-time code, `meta import`
for native_decide/#eval, `import all` of core for decide/rfl, a few proof edits) live as the
difference between the mechanical port of OLD_MAIN and the port commit OLD_PORT. `regen` ports
every file of the current checkout and merges that difference into it, file by file (3-way, with
`git merge-file`); files OLD_PORT added are copied. Conflicting files are listed (exit 1) and keep
conflict markers. Then build, fix what is new, and run `privatize`.

privatize: runs `lake shake` (or reads its report from --report) and turns every `public import`
of a local module that no public declaration needs into a private `import` (an unused import
stays, as a private import: the import graph is unchanged, only the re-export goes away). Imports
that must stay public can be marked `-- shake: keep` (see `lake shake --help`).
"""
import pathlib, re, subprocess, sys, tempfile

IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s")
SECTION = "@[expose] public section"


def header_end(lines):
    """(index of the first import or None, index after the last header line)."""
    depth, first, last = 0, None, None
    for i, line in enumerate(lines):
        s = line.strip()
        if depth:
            depth += s.count("/-") - s.count("-/")
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-"):
            depth = s.count("/-") - s.count("-/")
            continue
        if IMPORT.match(s):
            if first is None:
                first = i
            last = i
            continue
        return first, (last + 1 if last is not None else i)
    return first, (last + 1 if last is not None else len(lines))


def first_code_line(lines):
    depth = 0
    for i, line in enumerate(lines):
        s = line.strip()
        if depth:
            depth += s.count("/-") - s.count("-/")
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-") and not s.startswith(("/-!", "/--")):
            depth = s.count("/-") - s.count("-/")
            continue
        return i
    return len(lines)


def is_ported(lines):
    i = first_code_line(lines)
    return i < len(lines) and lines[i].strip() == "module"


def port(text):
    lines = text.split("\n")
    if is_ported(lines):
        return text
    first, end = header_end(lines)
    out = []
    for i, line in enumerate(lines[:end]):
        if first is not None and i == first:
            out.append("module")
            out.append("")
        if IMPORT.match(line) and not line.startswith("public "):
            line = "public " + line
        out.append(line)
    if first is None:
        k = first_code_line(lines)
        out = lines[:k] + ["module"]
        end = k
    rest = lines[end:]
    while rest and not rest[0].strip():
        rest.pop(0)
    out += ["", SECTION, ""] + rest
    return "\n".join(out)


def files(args):
    for a in args or ["FV", "FVTest", "corpus/dsl/Corpus"]:
        p = pathlib.Path(a)
        yield from (sorted(p.rglob("*.lean")) if p.is_dir() else [p])


LOCAL = ("FV", "FVTest", "Corpus")
LIBS = ("FV/", "FVTest/", "corpus/dsl/")


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, check=True).stdout


def lean_files(rev):
    out = git("ls-tree", "-r", "--name-only", rev).decode().split("\n")
    return {p for p in out if p.endswith(".lean") and p.startswith(LIBS)}


def regen(old_main, old_port):
    """Port the checkout and merge in OLD_PORT's fix-ups over the mechanical port of OLD_MAIN."""
    base_files, port_files = lean_files(old_main), lean_files(old_port)
    conflicts, merged, n = [], 0, 0
    for f in files([]):
        p = str(f)
        new = port(f.read_text())
        if p in base_files and p in port_files:
            base = port(git("show", f"{old_main}:{p}").decode())
            ours = git("show", f"{old_port}:{p}").decode()
            if ours != base:
                with tempfile.TemporaryDirectory() as d:
                    for name, s in (("new", new), ("base", base), ("ours", ours)):
                        pathlib.Path(d, name).write_text(s)
                    r = subprocess.run(["git", "merge-file", "-p", f"{d}/new", f"{d}/base", f"{d}/ours"],
                                       capture_output=True, text=True)
                new = r.stdout
                merged += 1
                if r.returncode:
                    conflicts.append(p)
        if new != f.read_text():
            f.write_text(new)
            n += 1
    for p in sorted(port_files - base_files):
        if not pathlib.Path(p).exists():
            pathlib.Path(p).parent.mkdir(parents=True, exist_ok=True)
            pathlib.Path(p).write_text(git("show", f"{old_port}:{p}").decode())
            n += 1
    print(f"regen: {n} files written, fix-ups merged into {merged}, {len(conflicts)} conflicts")
    for p in conflicts:
        print("  conflict:", p)
    return 1 if conflicts else 0


def privatize(report, only=None):
    """Apply a `lake shake` report to the local imports: every `public import` of a local module
    that shake drops or re-adds as private becomes a private `import` (a dropped import stays, as
    a private import, so the import graph only loses re-exports), and every import shake adds
    (a module that needs something it used to see through a re-export) is added as shake says.
    Other suggestions (narrowing `Lean`/`Std` imports) are ignored. ONLY: restrict to these files."""
    cur, rep = None, {}
    for line in report.splitlines():
        if line.endswith(".lean:") and not line.startswith(" "):
            cur = line[:-1]
            rep[cur] = {"remove": [], "add": []}
            continue
        m = re.match(r"\s+(remove|add) #\[(.*)\]$", line)
        if m and cur:
            rep[cur][m.group(1)] += [s.strip() for s in m.group(2).split(",")]
    n_files = n_down = n_add = 0
    for f, r in rep.items():
        if only is not None and pathlib.Path(f).resolve() not in only:
            continue
        adds = set(r["add"])
        path = pathlib.Path(f)
        t = path.read_text()
        before = t
        for imp in r["remove"]:
            mm = re.fullmatch(r"public import (\S+)", imp)
            if mm and mm.group(1).split(".")[0] in LOCAL and f"public import {mm.group(1)}" not in adds:
                t, k = re.subn(rf"^public import {re.escape(mm.group(1))}[ \t]*$", f"import {mm.group(1)}",
                              t, count=1, flags=re.M)
                n_down += k
        def covered(a):
            # already there (or public where shake wants it private), or under an umbrella
            # import of the same kind (`public import Lean` covers `public import Lean.Message`)
            kind, _, mod = a.rpartition(" ")
            if mod.split(".")[0] == "Init":
                return True
            for k in {kind, "public " + kind if not kind.startswith("public") else kind}:
                for umb in [".".join(mod.split(".")[:i]) for i in range(1, len(mod.split(".")) + 1)]:
                    if re.search(rf"^{re.escape(k)} {re.escape(umb)}[ \t]*$", t, re.M):
                        if umb == mod or umb in ("Lean", "Std"):
                            return True
            return False
        new = [a for a in r["add"] if not covered(a)]
        if new:
            ls = t.split("\n")
            last = max(i for i, l in enumerate(ls[:400]) if IMPORT.match(l) or l.startswith("import all "))
            ls[last + 1:last + 1] = new
            t = "\n".join(ls)
            n_add += len(new)
        if t != before:
            path.write_text(t)
            n_files += 1
    print(f"privatize: {n_down} imports made private, {n_add} added, in {n_files} files")


GENERATED = re.compile(r"^-- Generated by|GENERATED by|\(generated, do not edit\)|generated; see there", re.M)


def unexpose(only):
    """`@[expose] public section` -> `public section` (definition bodies private unless the
    definition says `@[expose]`), except in generated files (their data is unfolded by kernel
    checks downstream) and meta sections."""
    n = 0
    for f in files([]):
        if only is not None and f.resolve() not in only:
            continue
        t = f.read_text()
        if GENERATED.search(t[:1500]):
            continue
        new = re.sub(r"^@\[expose\] public section$", "public section", t, count=1, flags=re.M)
        if new != t:
            f.write_text(new)
            n += 1
    print(f"unexpose: {n} files")


def main():
    args = sys.argv[1:]
    if args[:1] == ["regen"]:
        sys.exit(regen(args[1], args[2]))
    if args[:1] == ["unexpose"]:
        only = None
        if args[1:2] == ["--only"]:
            only = {pathlib.Path(x.replace(".", "/") + ".lean").resolve()
                    for x in pathlib.Path(args[2]).read_text().split()}
        unexpose(only)
        return
    if args[:1] == ["privatize"]:
        args, report, only = args[1:], None, None
        while args[:1] in (["--report"], ["--only"]):
            if args[0] == "--report":
                report = pathlib.Path(args[1]).read_text()
            else:
                only = {pathlib.Path(x.replace(".", "/") + ".lean").resolve()
                        for x in pathlib.Path(args[1]).read_text().split()}
            args = args[2:]
        if report is None:
            # --force: the modules need not be the package's whole default target
            report = subprocess.run(["lake", "shake", "--force", *args], capture_output=True,
                                    text=True).stdout
        privatize(report, only)
        return
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    todo = []
    for f in files(args):
        t = f.read_text()
        n = port(t)
        if n != t:
            todo.append(f)
            if not check:
                f.write_text(n)
    if check:
        print("\n".join(map(str, todo)))
        sys.exit(1 if todo else 0)
    print(f"ported {len(todo)} files")


if __name__ == "__main__":
    main()
