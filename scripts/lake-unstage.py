#!/usr/bin/env python3
"""Unstage `lake cache stage` directories into the Lake cache; where they hold differing copies of
a module, keep the copy that the most downstream work was built against.

usage: scripts/lake-unstage.py [--root DIR] STAGES

Runs `lake cache unstage` on every directory below STAGES that holds an outputs.jsonl, in path
order (Lake's cache keeps the first output it gets for an input hash). The full gate
(.github/workflows/full-gate.yml) builds an import that several shards of a wave share in each of
them, and Lean's output is not always reproducible (FV.Backend.Proof.StockValues differs on every
build, FV.Opt.Proof.RuleRestEmbedRotl sometimes), so one input hash can have several outputs.
Lake hashes the imports' .olean files into a module's input hash: whatever a shard built against
a copy that is not kept is out of date in every later job and is built again there (run
40769795369: `lake build FV.Opt.Proof.RuleAll` rebuilt 42 imports and took 3 h). For each such
input hash the copy kept is the one whose stages hold the most recorded seconds
(scripts/lake-module-peaks.tsv; 60 s without a record) of importers of the module that no stage
with another copy holds; ties keep the first copy. Modules are known by the last component of
their name (the .ltar header), so a shared last component can only overcount.
"""
import argparse, collections, importlib.util, json, os, pathlib, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent


def ltar_name(path):
    """Last name component of the module an .ltar holds (it starts with LTR4\\0<last>.trace\\0)."""
    try:
        with open(path, "rb") as f:
            head = f.read(300)
    except OSError:
        return None
    if not head.startswith(b"LTR4"):
        return None
    return head[5:].split(b"\0")[0].decode(errors="replace").removesuffix(".trace")


def read_stages(top):
    """[(stage dir, header line, {input hash: output})] in unstage order."""
    out = []
    for f in sorted(pathlib.Path(top).rglob("outputs.jsonl")):
        lines = f.read_text().splitlines()
        out.append((f.parent, lines[0] if lines else '""',
                    {h: o for h, o in map(json.loads, filter(None, lines[1:]))}))
    return out


def choose(stages, root):
    """[(input hash, output, stage dir, report line)] for every input hash the stages map to
    differing outputs, with the output to keep."""
    copies = collections.defaultdict(dict)  # hash -> {output (json): [stage dirs]}
    for s, _, entries in stages:
        for h, o in entries.items():
            copies[h].setdefault(json.dumps(o), []).append(s)
    # module outputs are one .ltar each; leave anything else to Lake (first copy)
    conflicts = {h: c for h, c in copies.items()
                 if len(c) > 1 and all(o.startswith('"') for o in c)}
    if not conflicts:
        return []
    spec = importlib.util.spec_from_file_location("lsb", ROOT / "scripts/lake-serial-build.py")
    lsb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lsb)
    _, mods, imports = lsb.load_modules(root)
    prof = lsb.load_profile([root / "scripts/lake-module-peaks.tsv"])
    by_last, rdeps = collections.defaultdict(set), collections.defaultdict(set)
    for m, ds in imports.items():
        by_last[m.rsplit(".", 1)[-1]].add(m)
        for d in ds:
            rdeps[d].add(m)
    entries = {s: e for s, _, e in stages}
    names = {}

    def staged(s):  # last name components of the modules stage s holds
        if s not in names:
            names[s] = {ltar_name(s / o) for o in entries[s].values() if isinstance(o, str)}
        return names[s]

    out = []
    for h, c in sorted(conflicts.items()):
        first = next(iter(c))
        name = ltar_name(c[first][0] / json.loads(first))
        desc, todo = set(), list(by_last.get(name, ()))
        while todo:
            for r in rdeps[todo.pop()]:
                if r not in desc:
                    desc.add(r)
                    todo.append(r)
        dlast = collections.defaultdict(list)
        for d in desc:
            dlast[d.rsplit(".", 1)[-1]].append(d)
        have = {o: set().union(*map(staged, ss)) & dlast.keys() for o, ss in c.items()}
        value = {}
        for o in c:
            only = have[o] - set().union(*(have[p] for p in c if p != o))
            value[o] = sum(prof.get(m, (0, 60.0))[1] for n in only for m in dlast[n])
        keep = max(c, key=lambda o: value[o])  # first copy on ties
        report = (f"non-reproducible: {name or '?'} (input {h}): keeping the copy of "
                  + " | ".join(f"{' '.join(s.name for s in c[o])} ({value[o]:.0f} s of importers)"
                               for o in sorted(c, key=lambda o: o != keep)))
        out.append((h, json.loads(keep), c[keep][0], report))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("stages")
    ap.add_argument("--root", default=str(ROOT), help="workspace whose modules and peaks to use")
    a = ap.parse_args()
    root = pathlib.Path(a.root).resolve()
    stages = read_stages(a.stages)
    dirs = [s for s, _, _ in stages]
    kept = choose(stages, root)
    with tempfile.TemporaryDirectory(dir=a.stages) as tmp:
        if kept:
            # unstaged first, so Lake's cache keeps these copies
            lines = [stages[0][1]]
            for h, o, s, report in kept:
                print(report)
                lines.append(json.dumps([h, o]))
                try:
                    os.link(s / o, pathlib.Path(tmp) / o)
                except OSError:
                    shutil.copy2(s / o, pathlib.Path(tmp) / o)
            (pathlib.Path(tmp) / "outputs.jsonl").write_text("\n".join(lines) + "\n")
            dirs.insert(0, pathlib.Path(tmp))
        for d in dirs:
            subprocess.run(["lake", "cache", "unstage", str(d)], cwd=root, check=True)
    print(f"unstaged {len(stages)} staging directories")
    return 0


if __name__ == "__main__":
    sys.exit(main())
