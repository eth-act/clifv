#!/usr/bin/env python3
"""Port the Lean sources to the module system, scripted so the port can be regenerated on any main.

usage: scripts/module-port.py [--check] [FILE_OR_DIR...]   (default: FV FVTest corpus/dsl/Corpus)
       scripts/module-port.py regen OLD_MAIN OLD_PORT       (run on a checkout of the new main)
       scripts/module-port.py unexpose [--only MODLIST]
       scripts/module-port.py list-exposed | apply-exposed   (scripts/module-port-exposed.tsv)
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
                merged += 1
                if r.returncode:
                    conflicts.append(p)       # keep the mechanical port of the new version
                else:
                    new = r.stdout
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
    return 0


EXPOSE_LIST = pathlib.Path(__file__).with_name("module-port-exposed.tsv")
DECL_NAME = re.compile(r"^\s*(?:@\[([^\]]*)\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec) )*def\s+(\S+)", re.M)


def list_exposed():
    """`file<TAB>name` of every `@[expose] def` in files that are not exposed wholesale."""
    out = []
    for f in files([]):
        t = f.read_text()
        if re.search(r"^@\[expose\] public section$", t, re.M):
            continue
        for m in DECL_NAME.finditer(t):
            if m.group(1) and re.search(r"\bexpose\b", m.group(1)):
                out.append(f"{f}\t{m.group(2)}")
    EXPOSE_LIST.write_text("\n".join(sorted(out)) + "\n")
    print(f"exposed: {len(out)} definitions listed in {EXPOSE_LIST.name}")


def apply_exposed():
    """Re-add `@[expose]` to the listed definitions (after `regen` kept a conflicting file's
    mechanical port, or after main renamed things: missing names are reported)."""
    want = {}
    for line in EXPOSE_LIST.read_text().splitlines():
        if line.strip():
            f, n = line.split("\t")
            want.setdefault(f, set()).add(n)
    added = missing = 0
    for f, names in want.items():
        p = pathlib.Path(f)
        if not p.exists():
            missing += len(names)
            continue
        t = p.read_text()
        for n in names:
            m = re.search(rf"^(\s*)(@\[([^\]]*)\]\s*)?((?:(?:private|protected|noncomputable|partial|unsafe|nonrec) )*def\s+{re.escape(n)}(?=[\s:(\[{{]))", t, re.M)
            if not m:
                missing += 1
                print("  missing:", f, n)
                continue
            if m.group(3) is not None and re.search(r"\bexpose\b", m.group(3)):
                continue
            if m.group(2):
                rep = m.group(1) + m.group(2).replace("@[", "@[expose, ", 1) + m.group(4)
            else:
                rep = m.group(1) + "@[expose] " + m.group(4)
            t = t[:m.start()] + rep + t[m.end():]
            added += 1
        p.write_text(t)
    print(f"apply-exposed: {added} added, {missing} missing")


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


SIMP_ATTRS = None


def simp_attrs():
    """`simp` and every simp set the sources register (`register_simp_attr`)."""
    global SIMP_ATTRS
    if SIMP_ATTRS is None:
        SIMP_ATTRS = {"simp", "csimp"}
        for f in files([]):
            SIMP_ATTRS |= set(re.findall(r"^register_simp_attr (\S+)", f.read_text(), re.M))
    return SIMP_ATTRS


DEF_LINE = re.compile(r"^(\s*)@\[([^\]]*)\]((?:\s*--[^\n]*\n)*\s*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec) )*def\b)", re.M)
DERIVING = re.compile(r"deriving\b[^\n]*\b(DecidableEq|BEq|Ord|Hashable|LT|LE)\b")


def static_expose(t):
    """Expose what importers must be able to unfold, as far as the source shows it:
    definitions in a simp set (`@[simp]`, `@[state_simp_rules]`, ...: simp needs their equation
    lemmas) and the derived DecidableEq/BEq/Ord/Hashable instances of inductives and structures
    (`decide` reduces them): such a type declaration is wrapped in `@[expose] section ... end`."""
    attrs = simp_attrs()

    def fix_def(m):
        names = {a.strip().split()[0] for a in m.group(2).split(",") if a.strip()}
        if "expose" in names or not names & attrs:
            return m.group(0)
        return f"{m.group(1)}@[expose, {m.group(2)}]{m.group(3)}"
    t = DEF_LINE.sub(fix_def, t)
    ls, out, i = t.split("\n"), [], 0
    while i < len(ls):
        l = ls[i]
        m = re.match(r"^(?:(?:@\[[^\]]*\]\s*)?(?:private |protected )?)(inductive|structure|class inductive)\b", l)
        if m:
            j = i + 1
            while j < len(ls) and (ls[j].startswith((" ", "\t")) or ls[j].startswith("deriving")):
                j += 1
            block = ls[i:j]
            # preceding doc comment / attributes stay attached to the declaration
            k = len(out)
            while k > 0:
                if out[k - 1].startswith("@["):
                    k -= 1
                elif out[k - 1].rstrip().endswith("-/"):
                    s = k - 1
                    while s >= 0 and not out[s].lstrip().startswith(("/--", "/-")):
                        s -= 1
                    if s < 0 or not out[s].lstrip().startswith("/--"):
                        break
                    k = s
                else:
                    break
            if DERIVING.search("\n".join(block)) and not re.search(r"^\s+private ", "\n".join(block), re.M):
                pre = out[k:]
                del out[k:]
                out += ["@[expose] section"] + pre + block + ["end"]
                i = j
                continue
        out.append(l)
        i += 1
    return "\n".join(out)


def unexpose(only):
    """`@[expose] public section` -> `public section` (definition bodies private unless the
    definition says `@[expose]`), except in generated files (their data is unfolded by kernel
    checks downstream), then static_expose."""
    n = 0
    for f in files([]):
        if only is not None and f.resolve() not in only:
            continue
        t = f.read_text()
        if GENERATED.search(t[:1500]):
            continue
        new = re.sub(r"^@\[expose\] public section$", "public section", t, count=1, flags=re.M)
        if new != t or not re.search(r"^@\[expose\] public section$", t, re.M):
            new = static_expose(new)
        if new != t:
            f.write_text(new)
            n += 1
    print(f"unexpose: {n} files")


def main():
    args = sys.argv[1:]
    if args[:1] == ["regen"]:
        sys.exit(regen(args[1], args[2]))
    if args[:1] == ["list-exposed"]:
        list_exposed()
        return
    if args[:1] == ["apply-exposed"]:
        apply_exposed()
        return
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
