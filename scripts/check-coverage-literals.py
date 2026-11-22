#!/usr/bin/env python3
"""Reject theorem-name literals in lean-link's driver outside its claim table (#1104, #1096 part 2(c)).

usage: scripts/check-coverage-literals.py [FILE.lean ...]   (default: FVTest/Link/LeanLinkMain.lean)

`lean-link` names the theorems covering an executable only through `FVTest/Link/Coverage.lean`
(`Claim`, the route table `routeClaims`, whose names `FVTest/Link/CoverageTest.lean` checks are
theorems). This lint fails if the code of a checked file (comments and doc comments removed) holds
a token that looks like a theorem name lean-link prints: one ending in or containing `_correct`,
`_total`, `bundle_correct`, `binary_correct`, `_refines`, `_accepts` or `OkB_ld`. So a route cannot
print a theorem name without going through its `Claim`. Exit 1 with one line per hit.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT = [ROOT / "FVTest/Link/LeanLinkMain.lean"]
NAME = re.compile(
    r"[A-Za-z0-9_.']*(?:_correct|_total|bundle_correct|binary_correct|_refines|_accepts|OkB_ld)"
    r"[A-Za-z0-9_']*")


def strip_comments(src: str) -> str:
    """The code of a Lean file: block comments (nested, doc comments included) and line comments
    replaced by spaces, string literals kept (so their contents are checked), lines kept."""
    out = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(src[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
        elif src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            if c == '"':
                in_str = True
            out.append(c)
            i += 1
    return "".join(out)


def hits(src: str) -> list[tuple[int, str]]:
    """(line, token) for every theorem-name-like token in the code of `src`."""
    found = []
    for lineno, line in enumerate(strip_comments(src).split("\n"), 1):
        for m in NAME.finditer(line):
            found.append((lineno, m.group(0)))
    return found


def main(argv: list[str]) -> int:
    files = [Path(a) for a in argv] or DEFAULT
    bad = 0
    for f in files:
        for lineno, tok in hits(f.read_text()):
            print(f"{f}:{lineno}: theorem-name literal {tok!r} outside FVTest/Link/Coverage.lean "
                  "(name it through a Claim of the route table)")
            bad += 1
    if bad:
        return 1
    print(f"check-coverage-literals: ok ({', '.join(str(f.relative_to(ROOT)) if f.is_absolute() and ROOT in f.parents else str(f) for f in files)})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
