#!/usr/bin/env python3
"""Statement/axiom fingerprints (scripts/shake/Sigs.lean) of FV, FVTest and Corpus, and their
comparison before/after an import-only change.

usage: scripts/shake/sigs.py collect OUT.tsv      (after building every module)
       scripts/shake/sigs.py diff [--allow-moves] BEFORE.tsv AFTER.tsv

diff:
Auxiliary constants (AUX: equation lemmas, match splitters, ...) are not compared. Fails (exit 1)
if a constant appears or disappears, or changes module (unless --allow-moves:
moving declarations to another module), kind or type, if a
definition's or opaque's value changes, or if a theorem's axiom set changes. Theorems whose proof
term changed (same statement and axioms) are counted and listed, but do not fail the check.
"""
import pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))


def load(path, strip_private=False):
    """name -> (module, kind, type hash, value hash, axioms). With strip_private, private names
    (`_private.<module>.0.x`) are keyed by `x` (so that moving them is not a rename); private
    names that several modules declare keep their full name."""
    rows = {}
    lines = [line.rstrip("\n").split("\t") for line in open(path)]
    count, short = {}, {}
    for mod, name, *_ in lines:
        count[name] = count.get(name, 0) + 1
        mo = re.match(r"_private\.(.*?)\.0\.(.*)$", name)
        if mo:
            short.setdefault(mo.group(2), set()).add(mod)
    for mod, name, kind, th, vh, ax in lines:
        # a name declared in several modules that no module imports together: keyed per module
        key = name if count[name] == 1 else f"{name} @{mod}"
        mo = re.match(r"_private\.(.*?)\.0\.(.*)$", name)
        if strip_private and mo and len(short[mo.group(2)]) == 1:
            key = "private " + mo.group(2)
        rows[key] = (mod, kind, th, vh, ax)
    return rows


# Auxiliary constants Lean generates on demand (equation lemmas, unfolding lemmas, match
# splitters and their equations, congruence lemmas) in whichever module first needs them: an
# import change can move them or create them in another module. And `noConfusion`/
# `noConfusionType` of an inductive, whose universe parameter's hygienic name names the module.
AUX = re.compile(r"\.(eq_\d+|eq_def|eq_unfold|splitter|congr_simp|congr_eq_\d+|fun_cases|induct|noConfusion|noConfusionType)(\b|$)")


def main():
    if sys.argv[1] == "collect":
        import shake
        mods = shake.all_modules()
        n = shake.lean_batches("scripts/shake/Sigs.lean", mods, sys.argv[2], tag="sigs")
        print(f"sigs: {len(mods)} modules in {n} environments -> {sys.argv[2]}")
        return 0
    moves_ok = "--allow-moves" in sys.argv
    paths = [x for x in sys.argv[2:] if not x.startswith("--")]
    b, a = load(paths[0], moves_ok), load(paths[1], moves_ok)
    is_aux = lambda key: bool(AUX.search(key.split(" @")[0]))
    aux = sum(1 for n in b.keys() | a.keys() if is_aux(n) and b.get(n) != a.get(n))
    b = {n: r for n, r in b.items() if not is_aux(n)}
    a = {n: r for n, r in a.items() if not is_aux(n)}
    bad = []
    for n in sorted(b.keys() - a.keys()):
        bad.append(f"removed {n}")
    for n in sorted(a.keys() - b.keys()):
        bad.append(f"added {n}")
    proofs, moved = [], []
    for n in sorted(b.keys() & a.keys()):
        (bm, bk, bt, bv, bx), (am, ak, at, av, ax) = b[n], a[n]
        if bm != am:
            (moved if moves_ok else bad).append(f"moved {n}: {bm} -> {am}")
        if (bk, bt) != (ak, at):
            bad.append(f"changed {n}: {(bm, bk, bt)} -> {(am, ak, at)}")
        elif bk != "theorem" and bv != av:
            bad.append(f"value changed {n} ({bk})")
        elif bk == "theorem":
            if bx != ax:
                bad.append(f"axioms changed {n}: [{bx}] -> [{ax}]")
            elif bv != av:
                proofs.append(n)
    kinds = {}
    for _, k, *_ in b.values():
        kinds[k] = kinds.get(k, 0) + 1
    thm = kinds.get("theorem", 0)
    print(f"constants {len(b)} -> {len(a)} ({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))}); "
          f"differences {len(bad)}; moved to another module {len(moved)}; theorems with the same statement and axioms but another proof "
          f"term {len(proofs)}/{thm}; auxiliary constants (not compared) that differ {aux}")
    for x in bad[:50]:
        print("  " + x)
    for x in proofs[:20]:
        print("  proof term changed: " + x)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
