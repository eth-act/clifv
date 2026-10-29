#!/usr/bin/env python3
"""Port Lean sources to the module system, mechanically (idempotent).

usage: scripts/module-port.py [--check] [FILE_OR_DIR...]   (default: FV FVTest corpus/dsl/Corpus)

Each file that does not start with `module` gets
  * `module` before its first import (after leading comments),
  * `public import M` for every `import M`,
  * `@[expose] public section` after the imports: every declaration stays public and every
    definition body stays unfoldable by importers, as before the port; theorem proofs become
    private, so a proof-only edit no longer changes the module's public interface.
Files that need more (`meta` imports or definitions for elaboration-time code, `import all`) are
edited by hand after the mechanical step; the script leaves files that start with `module` alone.
--check lists the files that are not ported and exits 1 if there are any.
"""
import pathlib, re, sys

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


def main():
    args = sys.argv[1:]
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
