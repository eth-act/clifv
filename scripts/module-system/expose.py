#!/usr/bin/env python3
"""Re-expose the definitions a failed build needs.

usage: expose.py INDEX LOG...      (INDEX: declidx.lean output for the closure; LOG: build logs)

Candidates per error: names Lean reports directly (`Invalid simp theorem `X``, `failed to unfold
`X``, "not unfolded because their definition is not exposed: X ↦", `Invalid rewrite`), else every
identifier in the error text that names an indexed definition (decide/rfl/kernel failures print the
stuck term, which mentions the definitions it could not unfold). Each chosen definition gets
`@[expose]` at its declaration (merged into an existing `@[...]`). Prints `category<TAB>name<TAB>
module` per definition exposed (category: simp/unfold, rfl-note, rewrite, reduction, other).
"""
import collections, pathlib, re, sys

ROOT = pathlib.Path("/home/user/workspace/repo")
args = sys.argv[1:]
CLOSURE = "--closure" in args
FILES = "--files" in args
args = [a for a in args if a not in ("--closure", "--files")]
idx_path, logs = args[0], args[1:]
MECH = pathlib.Path("/home/user/workspace/port-mech")
_shift = {}


def path_of(root, mod):
    p = root / (mod.replace(".", "/") + ".lean")
    return root / "corpus/dsl" / (mod.replace(".", "/") + ".lean") if mod.startswith("Corpus.") else p


def header_len(p):
    try:
        ls = p.read_text().split("\n")
    except OSError:
        return 0
    return max([i for i, l in enumerate(ls[:400]) if re.match(r"^(public\s+)?(meta\s+)?import\s", l)] or [0])


def shift(mod):
    if mod not in _shift:
        _shift[mod] = header_len(path_of(ROOT, mod)) - header_len(path_of(MECH, mod))
    return _shift[mod]
by_full, by_short = {}, collections.defaultdict(list)
for line in open(idx_path):
    f = line.rstrip("\n").split("\t")
    if len(f) < 4:
        continue
    mod, name, ln, kind = f[0], f[1], int(f[2]), f[3]
    src = f[4] if len(f) > 4 else "cur"
    if src == "mech":
        ln += shift(mod)
    by_full[name] = (mod, ln, kind)
    parts = name.split(".")
    for i in range(len(parts)):
        by_short[".".join(parts[i:])].append(name)

import importlib.util
_spec = importlib.util.spec_from_file_location("lsb", ROOT / "scripts/lake-serial-build.py")
_lsb = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_lsb)
_, _mods, _imports = _lsb.load_modules(ROOT)


def modname_of(path):
    p = path[len("corpus/dsl/"):] if path.startswith("corpus/dsl/") else path
    return p[:-5].replace("/", ".")


def closure(m):
    seen, todo = set(), [m]
    while todo:
        x = todo.pop()
        if x in seen or x not in _imports:
            continue
        seen.add(x)
        todo.extend(_imports[x])
    return seen


ERR = re.compile(r"^error: ([^:\n]+\.lean):\d+:\d+: (.*?)(?=^error|^warning|^info|^Some required|\Z)", re.M | re.S)
IDENT = re.compile(r"[A-Za-z_«][\w.'«»!?₀-₉]*")
chosen = {}
chosen_from = {}
rexpose_files = set()
for log in logs:
    txt = pathlib.Path(log).read_text(errors="replace")
    for m in ERR.finditer(txt):
        msg = m.group(2)
        direct = []
        for pat, cat in ((r"Invalid simp theorem `([^`]+)`", "simp/unfold"),
                         (r"failed to unfold `([^`]+)`", "simp/unfold"),
                         (r"Expected a definition with an exposed body", None)):
            if cat:
                direct += [(x, cat) for x in re.findall(pat, msg)]
        note = re.search(r"not exposed:\n((?:\s+\S+ ↦ \d+\n?)+)", msg)
        if note:
            direct += [(x, "rfl-note") for x in re.findall(r"^\s+(\S+) ↦", note.group(1), re.M)]
        if "Invalid rewrite argument" in msg:
            direct += [(x, "rewrite") for x in re.findall(r"`([^`\s]+)", msg)[:1]]
        if direct:
            cands = direct
        else:
            cat = "reduction" if re.search(r"decide|rfl|definitional|kernel|reduce|unsolved goals|mismatch", msg) else "other"
            cands = []
            for tok in set(IDENT.findall(msg)):
                parts = tok.strip("@").split(".")
                for i in range(len(parts)):
                    for j in range(i + 1, len(parts) + 1):
                        cands.append((".".join(parts[i:j]), cat))
        for base in re.findall(r"([\w.]*\binst(?:DecidableEq|BEq|Ord|Hashable|Repr|Inhabited|LT|LE)\w*)\.\w+", msg):
            for n in sorted(set(([base] if base in by_full else []) + by_short.get(base, []))):
                rexpose_files.add(by_full[n][0])
        failing = modname_of(m.group(1))
        scope = closure(failing) if failing else None
        if not direct and re.search(r"exported from the current module|decide|rfl|definitional|unsolved goals|mismatch|made no progress", msg):
            # same-module definitions the failing proof mentions: an exported theorem may only
            # unfold exposed definitions, also from its own module
            try:
                src = path_of(ROOT, failing).read_text().split("\n")
                L = int(re.search(rf"^error: {re.escape(m.group(1))}:(\d+):", m.group(0), re.M).group(1)) - 1
                s = L
                while s > 0 and not re.match(r"^(@\[|theorem |lemma |private theorem |def |instance |example)", src[s]):
                    s -= 1
                for tok in set(IDENT.findall("\n".join(src[s:L + 3]))):
                    for x in {tok, tok.split(".")[-1]}:
                        ns = [k for k in by_short.get(x, []) if by_full[k][0] == failing]
                        if not ns and scope is not None:
                            ns = [k for k in by_short.get(x, []) if by_full[k][0] in scope]
                        if 0 < len(ns) <= 3:
                            cands += [(k, "same-module (exported proof)") for k in ns]
            except (OSError, AttributeError, ValueError):
                pass
        if not direct and "exported from the current module" in msg:
            insts = [n for n, v in by_full.items() if v[0] == failing and v[2] == "instance"]
            cands += [(n, "instance (same module)") for n in insts]
        scope = closure(failing) if failing else None
        for x, cat in set(cands):
            x = x.strip("@")
            names = sorted(set(([x] if x in by_full else []) + by_short.get(x, [])))
            if scope is not None:
                names = [n for n in names if by_full[n][0] in scope]
            if len(names) > (8 if cat != "reduction" else 3):   # too ambiguous: skip
                continue
            for n in names:
                if by_full[n][2] == "instance" and cat in ("other", "reduction"):
                    continue
                chosen.setdefault(n, cat)
                chosen_from.setdefault(n, failing)

def body_refs(n):
    """Definitions of n's own module that n's source text mentions (depth 1)."""
    mod, ln, kind = by_full[n]
    p = path_of(ROOT, mod)
    try:
        ls = p.read_text().split("\n")
    except OSError:
        return []
    i = ln - 1
    body = []
    for j in range(i, min(i + 200, len(ls))):
        if j > i and re.match(r"^(@\[|def |theorem |instance |abbrev |structure |inductive |end |namespace |section)", ls[j]):
            break
        body.append(ls[j])
    out = set()
    for tok in set(IDENT.findall("\n".join(body))):
        for x in {tok, tok.split(".")[-1]}:
            names = [k for k in by_short.get(x, []) if by_full[k][0] == mod and k != n]
            if 0 < len(names) <= 3:
                out.update(names)
    return out


DECL = re.compile(r"^(\s*)(@\[([^\]]*)\]\s*)?((?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public) )*)(def|instance|opaque|abbrev)\b")
for n in list(chosen):
    for d in body_refs(n):
        chosen.setdefault(d, "dependency")
if CLOSURE:
    seeds = [n for n, c in chosen.items() if c not in ("instance (same module)",)]
    if seeds:
        T = pathlib.Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"
        env = dict(__import__("os").environ, LEAN_PATH=f"{MECH}/.lake/build/lib/lean:{T}/lib/lean")
        r = __import__("subprocess").run(["lean", "--run", "/home/user/ms/defdeps.lean",
                                          "FVTest.Backend.Main", *seeds], cwd=MECH, env=env,
                                         capture_output=True, text=True)
        for line in r.stdout.splitlines():
            n = line.split("\t")[0]
            if n in by_full:
                chosen.setdefault(n, "closure")
if FILES:
    # last resort: `import all` (in the failing module) of every module of its closure that
    # defines something the error text names; the failing module then sees their private bodies,
    # nobody else does
    need = collections.defaultdict(set)
    for n, (mod_f) in chosen_from.items():
        need[mod_f].add(by_full[n][0])
    for mod_f, ms in need.items():
        p = path_of(ROOT, mod_f)
        ls = p.read_text().split("\n")
        have = {l.split()[-1] for l in ls if l.startswith("import all ")}
        add = [f"import all {m}" for m in sorted(ms) if m != mod_f and m not in have]
        if add:
            last = max(i for i, l in enumerate(ls[:400]) if re.match(r"^(public\s+)?(meta\s+)?import\s", l))
            ls[last + 1:last + 1] = add
            p.write_text("\n".join(ls))
            for a in add:
                print(f"import all (proof needs private bodies)\t{a.split()[-1]}\t{mod_f}")
    chosen = {}
    rexpose_files = set()
for mod in sorted(rexpose_files):
    p = path_of(ROOT, mod)
    s = p.read_text()
    s2 = re.sub(r"^public section$", "@[expose] public section", s, count=1, flags=re.M)
    if s2 != s:
        p.write_text(s2)
        print(f"{'file re-exposed (unresolved)' if FILES else 'derived instance (file re-exposed)'}\t{mod}\t{mod}")
edits = collections.defaultdict(list)
for n, cat in chosen.items():
    mod, ln, kind = by_full[n]
    p = ROOT / (mod.replace(".", "/") + ".lean")
    if mod.startswith("Corpus."):
        p = ROOT / "corpus/dsl" / (mod.replace(".", "/") + ".lean")
    edits[p].append((ln, n, cat, mod))
for p, es in edits.items():
    if re.search(r"^@\[expose\] public section$", p.read_text(), re.M):
        continue        # still exposed wholesale (generated files)
    ls = p.read_text().split("\n")
    for ln, n, cat, mod in sorted(es, reverse=True):
        i = ln - 1
        # from the reported start, skip doc comments to the declaration's first line
        short = n.split(".")[-1]
        hit = None
        for j in range(max(0, i), min(i + 40, len(ls))):
            m = DECL.match(ls[j])
            if m:
                if by_full[n][2] == "instance" or re.search(rf"[\s.]{re.escape(short)}(\s|$|:)", ls[j]):
                    hit = (j, m)
                break
        if hit is None and by_full[n][2] != "instance":
            parts = n.split(".")
            for k in range(1, len(parts) + 1):        # longest written suffix first
                suf = ".".join(parts[-k:]) if False else None
            for k in range(len(parts), 0, -1):
                suf = ".".join(parts[len(parts) - k:])
                for j, l in enumerate(ls):
                    m = DECL.match(l)
                    if m and re.search(rf"\b(def|opaque|instance)\s+{re.escape(suf)}(\s|$|:)", l):
                        hit = (j, m)
                        break
                if hit:
                    break
        if hit is None:
            print(f"notfound\t{n}\t{mod}", file=sys.stderr)
            continue
        j, m = hit
        if m.group(5) == "abbrev":
            continue
        attrs = m.group(3)
        if attrs is not None and re.search(r"\bexpose\b", attrs):
            continue
        prev = j - 1
        while prev >= 0 and ls[prev].strip().startswith("--"):
            prev -= 1
        if attrs is None and prev >= 0 and re.fullmatch(r"\s*@\[[^\]]*\]\s*", ls[prev]):
            if re.search(r"\bexpose\b", ls[prev]):
                continue
            ls[prev] = ls[prev].replace("@[", "@[expose, ", 1)
        elif attrs is not None:
            ls[j] = ls[j].replace("@[", "@[expose, ", 1)
        else:
            ls[j] = m.group(1) + "@[expose] " + ls[j][len(m.group(1)):]
        print(f"{cat}\t{n}\t{mod}")
    p.write_text("\n".join(ls))
