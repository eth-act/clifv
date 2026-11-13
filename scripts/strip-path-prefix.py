#!/usr/bin/env python3
"""Remove a path prefix from text files, as a literal string.

usage: strip-path-prefix.py PREFIX FILE…

Every occurrence of PREFIX in each FILE is removed (`/w/clifv/examples/x` becomes `examples/x`
for PREFIX `/w/clifv/`). scripts/regen-crate-proofs.sh uses it on the generated crate proofs,
where link-check names the executable by its absolute path: the committed files must not depend
on where the checkout is (#984). PREFIX is not a pattern: a checkout path may hold `[`, `.`,
`|`, `&` or `\\`, which a `sed "s|$ROOT/||"` reads as syntax.

Exit status 1, naming the file, if a FILE still holds PREFIX without its trailing slashes
afterwards (the path in a form this script does not rewrite), or cannot be read or written.
"""
import sys


def strip(text, prefix):
    """(text without `prefix`, whether what is left still names the prefix's directory)."""
    out = text.replace(prefix, "")
    return out, prefix.rstrip("/") in out


def main(argv):
    if len(argv) < 2 or not argv[0].strip("/"):
        print(__doc__.strip().splitlines()[2], file=sys.stderr)
        return 2
    prefix, rc = argv[0], 0
    for path in argv[1:]:
        try:
            with open(path, encoding="utf-8") as f:
                text = f.read()
            out, left = strip(text, prefix)
            if out != text:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(out)
        except (OSError, UnicodeError) as e:
            print(f"strip-path-prefix: {path}: {e}", file=sys.stderr)
            rc = 1
            continue
        if left:
            print(f"strip-path-prefix: {path} still names {prefix.rstrip('/')}", file=sys.stderr)
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
