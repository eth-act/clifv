#!/usr/bin/env python3
"""Summarize one extraction run (extract/scripts/extract.sh) into report.json.

usage: report.py RUN_DIR [--out report.json]

Seeded from the 2026-11-17 census summarize.py
(/data/clifv-aeneas-cranelift-20261117/census/evidence.tar.zst).
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re

EXTRACT = Path(__file__).resolve().parent.parent
GENERATED = EXTRACT / "lean/Generated"
MODELS = [EXTRACT / "lean/ClifvExtract/TypesExternal.lean", EXTRACT / "lean/ClifvExtract/FunsExternal.lean"]
CRATES = ["clifv_extract_entry", "cranelift_codegen", "cranelift_reader", "cranelift_entity",
          "cranelift_bforest", "cranelift_bitset", "cranelift_control", "regalloc2"]
HASH_ITER = {"iter", "iter_mut", "keys", "values", "values_mut", "drain", "into_iter", "retain", "extract_if"}
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def patterns(path):
    if not path.exists():
        return []
    return [line.split("\t")[0].strip() for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


def name_elems(name):
    """Charon `Name` (list of PathElem) as pattern-comparable strings."""
    out = []
    for e in name:
        if "Ident" in e:
            out.append(e["Ident"][0])
        elif "Impl" in e:
            out.append("{impl}" + json.dumps(e["Impl"], sort_keys=True))
        else:
            out.append(json.dumps(e, sort_keys=True))
    return out


def split_pattern(p):
    """Split a name pattern on `::` outside `{}`/`<>`."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(p):
        c = p[i]
        if c in "{<":
            depth += 1
        elif c in "}>":
            depth -= 1
        if depth == 0 and p.startswith("::", i):
            parts.append(cur); cur = ""; i += 2; continue
        cur += c; i += 1
    parts.append(cur)
    return parts


def impl_trait(elem):
    """For an `{impl}` path element, the trait name string (last ident) if any."""
    m = re.search(r'"trait_decl_id"|"Trait"', elem)
    return m is not None


def pattern_matches(pattern, rendered, elems):
    """Approximate Charon's name matcher: prefix match by segments; a pattern that starts with an
    impl block (`{impl Trait for _}`) matches any item under an impl of that trait (by the
    rendered impl segment)."""
    parts = split_pattern(pattern)
    if parts[0].startswith("{impl "):
        trait = re.match(r"\{impl ([^ <]+)", parts[0])[1]
        return f"{{impl {trait}" in rendered or f"{{impl {trait.split('::')[-1]}" in rendered
    segs = split_pattern(rendered)
    if len(parts) > len(segs):
        return False
    return all(p in ("_", "*") or p == s or (p.startswith("{") and s.startswith("{")) and p == s
               for p, s in zip(parts, segs))


def diagnostics(path, kinds):
    if not path.exists():
        return []
    text = ANSI.sub("", path.read_text(errors="replace"))
    sections = re.split(r"(?m)^\s*(?=(?:\[(?:Error|Warn |Info )\]|error:|warning:|Fatal error:))", text)
    out = []
    for rec in sections:
        if not rec.startswith(kinds):
            continue
        lines = rec.splitlines()
        src = next((ln.strip() for ln in lines if ln.startswith("Source:") or ln.lstrip().startswith("-->")), None)
        emitter = next((ln.strip() for ln in lines if ln.startswith("Compiler source:")), None)
        out.append({"message": lines[0][:600], "source": src, "emitter": emitter})
    return out


def families(records):
    groups = defaultdict(list)
    for r in records:
        key = re.sub(r"'(?:[^']|'[a-z]\b)*'", "'<item>'", r["message"])
        key = re.sub(r"`[^`]*`", "`<item>`", key)
        key = re.sub(r"\[[\d, ]+\]", "[<ids>]", key)
        key = re.sub(r"\b\d+\b", "<n>", key)
        groups[key, r["emitter"]].append(r["source"])
    return sorted(({"message": k[0], "emitter": k[1], "count": len(v), "spans": v[:3]}
                   for k, v in groups.items()), key=lambda f: -f["count"])


def lean_defined_names(paths):
    names = set()
    for p in paths:
        if p.exists():
            for m in re.finditer(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|opaque|structure|inductive|abbrev)\s+(\S+)", p.read_text()):
                names.add(m[1])
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run", type=Path)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    run = args.run
    exit_of = lambda tool: int((run / f"{tool}.exit").read_text()) if (run / f"{tool}.exit").exists() else None
    report = {"run": str(run), "charon_exit": exit_of("charon"), "aeneas_exit": exit_of("aeneas")}
    cdiag = diagnostics(run / "charon.log", ("error:", "Fatal error:"))
    adiag = diagnostics(run / "aeneas.log", ("[Error]", "Fatal error:"))
    report["charon_error_families"] = families(cdiag)
    report["error_families"] = families(adiag)
    report["aeneas_fatal"] = any(r["message"].startswith("Fatal error") for r in adiag)

    llbc_path = run / "entry.llbc"
    local = []
    if llbc_path.exists():
        crate = json.loads(llbc_path.read_text())
        report["llbc_has_errors"] = crate.get("has_errors")
        t = crate["translated"]
        funs = [f for f in t["fun_decls"] if f is not None]
        local = [f for f in funs if f["item_meta"]["is_local"] or name_elems(f["item_meta"]["name"])[0] in CRATES]
        report["llbc_local_functions"] = len(local)
        report["hash_iteration_sites"] = hash_iteration_sites(t, funs)
    else:
        report["llbc_has_errors"] = None

    translation = next(GENERATED.rglob("translation.json"), None) if GENERATED.exists() else None
    emitted = {}
    if translation:
        for row in json.loads(translation.read_text()).get("functions", []):
            if not row.get("loop"):
                emitted[row["def_id"]] = row
    failures_path = next(GENERATED.rglob("failures.json"), None) if GENERATED.exists() else None
    report["failed_items"] = json.loads(failures_path.read_text()) if failures_path else None

    opaque_cfg, overrides = patterns(EXTRACT / "opaque.txt"), patterns(EXTRACT / "overrides.txt")
    per_crate = {c: {"local_functions": 0, "lean_body": 0} for c in CRATES}
    split = {"configured": [], "override": [], "unexpected": []}
    for f in local:
        elems = name_elems(f["item_meta"]["name"])
        rendered = render_name(f["item_meta"]["name"])
        c = per_crate.setdefault(elems[0], {"local_functions": 0, "lean_body": 0})
        c["local_functions"] += 1
        row = emitted.get(f["def_id"])
        if row is not None and not row.get("is_opaque"):
            c["lean_body"] += 1
            continue
        if any(pattern_matches(p, rendered, elems) for p in overrides):
            split["override"].append(rendered)
        elif any(pattern_matches(p, rendered, elems) for p in opaque_cfg):
            split["configured"].append(rendered)
        else:
            split["unexpected"].append(rendered)
    report["crates"] = per_crate
    report["opaque_local_functions"] = {k: sorted(v) for k, v in split.items()}
    report["opaque_local_counts"] = {k: len(v) for k, v in split.items()}

    lean_files = list(GENERATED.rglob("*.lean")) if GENERATED.exists() else []
    report["sorry_count"] = sum(len(re.findall(r"\bsorry\b", p.read_text())) for p in lean_files)
    defined = lean_defined_names(MODELS)
    missing = []
    for p in lean_files:
        if p.name.endswith("External_Template.lean"):
            for m in re.finditer(r"(?m)^axiom\s+(\S+)", p.read_text()):
                if m[1] not in defined:
                    missing.append(m[1])
    report["missing_external_models"] = sorted(set(missing))
    out = args.out or run / "report.json"
    out.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in ("charon_exit", "aeneas_exit", "llbc_has_errors", "aeneas_fatal",
                                             "sorry_count", "opaque_local_counts")}, indent=1))
    print("missing_external_models", len(report["missing_external_models"]),
          "failed_items", None if report["failed_items"] is None else len(report["failed_items"]))
    for f in report["error_families"][:25]:
        print(f'{f["count"]:6} {f["message"][:150]}  [{f["emitter"]}]')


def render_name(name):
    out = []
    for e in name:
        if "Ident" in e:
            out.append(e["Ident"][0])
        elif "Impl" in e:
            out.append(render_impl(e["Impl"]))
        else:
            out.append("_")
    return "::".join(out)


def render_impl(impl):
    """Best-effort `{impl Trait for Ty}` / `{Ty}` rendering of an impl path element."""
    s = json.dumps(impl)
    trait = re.search(r'"Trait":\s*\{[^}]*?"id":\s*(\d+)', s)
    return "{impl " + (f"#trait{trait[1]}" if trait else "") + "}"


def hash_iteration_sites(t, funs):
    """Call sites of hashbrown iteration methods (Step 8 audit)."""
    names = {}
    for f in funs:
        names[f["def_id"]] = name_elems(f["item_meta"]["name"])
    sites = []
    for f in funs:
        body = json.dumps(f.get("body"))
        for m in re.finditer(r'"Regular":\s*(\d+)', body):
            callee = names.get(int(m[1]))
            if callee and callee[0] == "hashbrown" and callee[-1] in HASH_ITER:
                sites.append({"caller": "::".join(name_elems(f["item_meta"]["name"])), "callee": "::".join(callee)})
    return sites


if __name__ == "__main__":
    main()
