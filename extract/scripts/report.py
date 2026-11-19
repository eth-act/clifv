#!/usr/bin/env python3
"""Summarize one extraction run (extract/scripts/extract.sh) into report.json.

usage: report.py RUN_DIR [--out report.json] [--hash-sites FILE]

Inputs: RUN_DIR/{charon,aeneas}.{log,exit}, RUN_DIR/entry.llbc, and the generated
extract/lean/Generated/{translation.json,failures.json,**/*.lean}.
Seeded from the 2026-11-17 census summarize.py
(/data/clifv-aeneas-cranelift-20261117/census/evidence.tar.zst).
"""
import argparse
from collections import defaultdict
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


def split_path(p):
    """Split a Rust path on `::` outside `{}`/`<>`/`()`."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(p):
        c = p[i]
        if c in "{<(":
            depth += 1
        elif c in "}>)":
            depth -= 1
        if depth == 0 and p.startswith("::", i):
            parts.append(cur); cur = ""; i += 2; continue
        cur += c; i += 1
    parts.append(cur)
    return parts


def pattern_matches(pattern, rust_name):
    """Approximation of Charon's name matcher on Aeneas' `rust_name`s: segment-wise prefix
    match where `_` matches any segment; a pattern starting with an impl block
    (`{impl Trait for _}`) matches every item under an impl of that trait."""
    parts = split_path(pattern)
    m = re.match(r"\{impl ([^<\s]+)", parts[0])
    if m:
        return any(re.match(r"\{impl " + re.escape(m[1]) + r"\b", seg) for seg in split_path(rust_name))
    segs = split_path(rust_name)
    if len(parts) > len(segs):
        return False
    return all(p in ("_", "*") or p == s for p, s in zip(parts, segs))


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


def defined_names(paths):
    names = set()
    for p in paths:
        if p.exists():
            for m in re.finditer(r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|partial\s+)*"
                                 r"(?:def|opaque|structure|inductive|abbrev|instance)\s+(\S+)", p.read_text()):
                names.add(m[1])
    return names


def llbc_name(name):
    out = []
    for e in name:
        if "Ident" in e:
            out.append(e["Ident"][0])
        elif "Impl" in e:
            out.append("{impl}")
        else:
            out.append("_")
    return out


def hash_iteration_sites(lean_files):
    """Calls of hashbrown iteration methods (Step 8 audit), from the generated Lean: for
    every generated definition (headed by its `/-- [rust::name]` docstring), the hashbrown
    iteration functions it calls. (The LLBC deduplicates its function references, so the
    generated code is the simpler source.)"""
    call = re.compile(r"\bhashbrown(?:_\d+)?\.(?:map|set)\.\w+\.(" + "|".join(sorted(HASH_ITER)) + r")\b")
    sites = []
    for p in lean_files:
        if p.name.endswith("_Template.lean"):
            continue
        text = p.read_text()
        heads = [(m.start(), m[1]) for m in re.finditer(r"/-- \[([^\]]+)\]", text)]
        for i, (start, caller) in enumerate(heads):
            end = heads[i + 1][0] if i + 1 < len(heads) else len(text)
            callees = sorted({m[0] for m in call.finditer(text, start, end)})
            if callees:
                sites.append({"caller": caller, "callees": callees})
    return sites


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run", type=Path)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--hash-sites", type=Path)
    args = ap.parse_args()
    run = args.run
    exit_of = lambda tool: int((run / f"{tool}.exit").read_text()) if (run / f"{tool}.exit").exists() else None
    report = {"run": str(run), "charon_exit": exit_of("charon"), "aeneas_exit": exit_of("aeneas")}
    report["charon_error_families"] = families(diagnostics(run / "charon.log", ("error:", "Fatal error:")))
    adiag = diagnostics(run / "aeneas.log", ("[Error]", "Fatal error:"))
    report["error_families"] = families(adiag)
    report["aeneas_fatal"] = (run / "aeneas.log").exists() and "Fatal error" in (run / "aeneas.log").read_text(errors="replace")

    # Inventory of the functions of the included crates, from the LLBC
    llbc_funs = []
    llbc_path = run / "entry.llbc"
    if llbc_path.exists():
        crate = json.loads(llbc_path.read_text())
        report["llbc_has_errors"] = crate.get("has_errors")
        funs = [f for f in crate["translated"]["fun_decls"] if f is not None]
        llbc_funs = [f for f in funs if llbc_name(f["item_meta"]["name"])[0] in CRATES]
        if args.hash_sites and GENERATED.exists():
            args.hash_sites.write_text(
                json.dumps(hash_iteration_sites(list(GENERATED.rglob("*.lean"))), indent=1) + "\n")
        del crate, funs
    else:
        report["llbc_has_errors"] = None

    translation = GENERATED / "translation.json"
    entries = {}
    if translation.exists():
        for row in json.loads(translation.read_text())["functions"]:
            if row.get("loop") is None:
                entries[row["def_id"]] = row
    failures_path = GENERATED / "failures.json"
    report["failed_items"] = json.loads(failures_path.read_text()) if failures_path.exists() else None

    opaque_cfg, overrides = patterns(EXTRACT / "opaque.txt"), patterns(EXTRACT / "overrides.txt")
    per_crate = {c: {"functions": 0, "lean_body": 0, "missing": 0} for c in CRATES}
    split = {"configured": [], "override": [], "unexpected": []}
    for f in llbc_funs:
        crate_name = llbc_name(f["item_meta"]["name"])[0]
        c = per_crate[crate_name]
        c["functions"] += 1
        row = entries.get(f["def_id"])
        if row is None:
            c["missing"] += 1
            name = "::".join(llbc_name(f["item_meta"]["name"]))
        elif not row["is_opaque"]:
            c["lean_body"] += 1
            continue
        else:
            name = row["rust_name"]
        if any(pattern_matches(p, name) for p in overrides):
            split["override"].append(name)
        elif f["item_meta"].get("opacity") == "Opaque" or any(pattern_matches(p, name) for p in opaque_cfg):
            split["configured"].append(name)
        else:
            split["unexpected"].append(name)
    report["crates"] = per_crate
    report["opaque_local_counts"] = {k: len(v) for k, v in split.items()}
    report["opaque_local_functions"] = {k: sorted(v) for k, v in split.items()}

    lean_files = list(GENERATED.rglob("*.lean")) if GENERATED.exists() else []
    report["sorry_count"] = sum(len(re.findall(r"\bsorry\b", p.read_text())) for p in lean_files)
    defined = defined_names(MODELS)
    missing = set()
    for p in lean_files:
        if p.name.endswith("External_Template.lean"):
            for m in re.finditer(r"(?m)^axiom\s+(\S+)", p.read_text()):
                if m[1] not in defined:
                    missing.add(m[1])
    report["missing_external_models"] = sorted(missing)

    out = args.out or run / "report.json"
    out.write_text(json.dumps(report, indent=1) + "\n")
    summary = {k: report[k] for k in ("charon_exit", "aeneas_exit", "llbc_has_errors", "aeneas_fatal",
                                      "sorry_count", "opaque_local_counts")}
    summary["failed_items"] = None if report["failed_items"] is None else len(report["failed_items"])
    summary["missing_external_models"] = len(report["missing_external_models"])
    summary["crates"] = per_crate
    print(json.dumps(summary, indent=1))
    for fam in report["error_families"][:25]:
        print(f'{fam["count"]:6} {fam["message"][:150]}  [{fam["emitter"]}]')


if __name__ == "__main__":
    main()
