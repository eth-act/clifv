#!/usr/bin/env python3
"""Capture stock AArch64 pre-JIT artifacts and compare the unmodified Lean backend."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from byte_compare import ELF, byte_diff

ROOT = Path(__file__).resolve().parent.parent
PIN = "46c23a87dac1465986a8ad53ba6a7ae49372857b"
TARGET = "aarch64-unknown-linux-gnu"


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def comparison(reference, lean, reference_relocs, lean_relocs):
    code = byte_diff(reference, lean)
    # Identity canonicalization only: %foo and foo designate the same symbol.
    def canonical(rows):
        return sorted((r["offset"], r["kind"], r["target"].removeprefix("%"), r["addend"]) for r in rows)
    relocs_equal = canonical(reference_relocs) == canonical(lean_relocs)
    return {"bytes": code, "relocations_equal": relocs_equal,
            "reference_relocations": reference_relocs, "lean_relocations": lean_relocs,
            "exact_code_and_relocations": code["equal"] and relocs_equal}


def settings_audit(variant):
    shared = {s["name"]: s["value"] for s in variant["flags"]}
    requested_features = [s for s in variant["isa_flags"] if s["value"] not in ("false", "0")]
    differences = []
    if shared.get("preserve_frame_pointers") == "false":
        differences.append("Stock omits optional leaf frames; Lean always preserves frame pointers")
    if shared.get("is_pic") == "false":
        differences.append("Stock is_pic=false; Lean instruction selection fixes is_pic=true")
    if shared.get("opt_level") != "none":
        differences.append("Stock optimization setting has no matching Lean configuration")
    if requested_features:
        differences.append("Requested ISA feature settings have no matching Lean CLI")
    return {"settings_parity_verified": False, "known_configuration_differences": differences,
            "requested_isa_features": requested_features,
            "note": "Bytes are measured against stock settings, not settings changed to improve agreement. Lean setting parity is not established."}


def command(argv, directory, name, env):
    directory.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    try:
        p = subprocess.run([str(a) for a in argv], capture_output=True, timeout=120, env=env, cwd=ROOT)
        status, stdout, stderr = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        status, stdout, stderr = "timeout", e.stdout or b"", e.stderr or b""
    (directory / (name + ".stdout")).write_bytes(stdout)
    (directory / (name + ".stderr")).write_bytes(stderr)
    result = {"argv": [str(a) for a in argv], "exit": status, "seconds": time.monotonic()-start}
    write(directory / (name + ".command.json"), result)
    return result


def one(path, out, env, binary):
    stock = ROOT / "third_party/wasmtime/cranelift/filetests/filetests/runtests"
    key = str(path.relative_to(stock)).replace("/", "__")
    directory = out / "files" / key
    directory.mkdir(parents=True)
    (directory / "original.clif").write_bytes(path.read_bytes())
    exported = directory / "reference"
    result = {"input": str(path), "case": key, "variants": []}
    result["export"] = command([binary, path, exported, TARGET], directory, "export", env)
    manifest = exported / "manifest.json"
    if not manifest.exists():
        result["status"] = "reference_export_failed"
        write(directory / "case.json", result)
        return result
    manifest = json.loads(manifest.read_text())
    result["status"] = "exported" if manifest["variants"] else "no_aarch64_configuration"
    for variant in manifest["variants"]:
        index = variant["index"]
        reference = exported / f"variant-{index}"
        dest = directory / f"variant-{index}"
        dest.mkdir()
        v = {**variant, "settings_audit": settings_audit(variant), "comparisons": []}
        names = variant["functions"]
        effective = []
        prepared_names = set()
        metadata_by_name = {}
        for artifact in sorted(reference.glob("*.json")):
            meta = json.loads(artifact.read_text())
            name = meta["name"]
            metadata_by_name[name] = (artifact, meta)
        # Include failed function's prepared input too; missing reference artifacts
        # remain explicit gaps. Trampolines are exported but not credited as Lean.
        original_effective = []
        for source in sorted(reference.glob("*.clif")):
            if source.name.endswith(".lean.clif"):
                continue
            text = source.read_text()
            import re
            match = re.search(r"^function\s+(\S+)\(", text, re.M)
            if match and match[1] in names:
                original_effective.append(text)
                adapted = source.with_name(source.stem + ".lean.clif")
                effective.append(adapted.read_text() if adapted.exists() else text)
                prepared_names.add(match[1])
        (dest / "effective.clif").write_text("\n\n".join(original_effective))
        input_file = dest / "lean-input.clif"
        input_file.write_text("\n\n".join(effective))
        v["reference_preparation_coverage"] = len(prepared_names)
        if not effective:
            v["status"] = "no_prepared_test_functions"
            if variant["eligible"]:
                v["comparisons"] = [{"name":n,"status":"reference_missing", "reason":variant["error"]} for n in names]
            result["variants"].append(v)
            continue
        lean = dest / "lean"
        lean.mkdir()
        v["lean_compile"] = command([ROOT / ".lake/build/bin/lean-backend", input_file, lean / "program.o",
            "--dump", lean / "dump", "--traps", lean / "traps.json"], dest, "lean", env)
        elf = ELF(lean / "program.o") if (lean / "program.o").exists() else None
        for name in names:
            row = {"name": name}
            artifact = metadata_by_name.get(name)
            lean_name = name.removeprefix("%")
            code_path = lean / "dump" / (lean_name + ".bin")
            if artifact is None:
                row.update(status="reference_missing", reason="Stock preparation/compilation stopped before this function")
            elif not code_path.exists():
                row.update(status="lean_missing", reason="Lean did not produce this function; see retained compile log and traps.json")
            else:
                source, meta = artifact
                lean_relocs = json.loads((lean / "dump" / (lean_name + ".relocs.json")).read_text())
                row.update(comparison(source.with_suffix(".bin").read_bytes(), code_path.read_bytes(), meta["relocations"], lean_relocs))
                row["status"] = "identical" if row["exact_code_and_relocations"] else "different"
                lean_traps = json.loads((lean / "dump" / (lean_name + ".traps.json")).read_text())
                row["trap_metadata"] = {"equal": meta["traps"] == lean_traps, "reference": meta["traps"], "lean": lean_traps}
                row["alignment"] = {"reference": meta["alignment"], "lean": 4, "equal": meta["alignment"] == 4,
                                    "basis": "Lean FnBin contains 4-byte words and Obj.lean concatenates functions in a .text section aligned to 4"}
                row["execution_metadata"] = {"reference_unwind": meta["unwind"], "reference_exception_call_sites": meta["exception_call_sites"],
                    "reference_exception_table_bytes":meta["exception_table_bytes"],
                    "reference_stack_maps": meta["stack_maps"], "equality_verified": False,
                    "lean_eh_frame_present": any(s["name"] == ".eh_frame" for s in elf.sections) if elf else False}
                if not row["bytes"]["equal"]:
                    offset = row["bytes"]["first_difference"] // 4 * 4
                    row["first_differing_instruction"] = {"offset":offset,
                        "reference_word":source.with_suffix(".bin").read_bytes()[offset:offset+4].hex(),
                        "lean_word":code_path.read_bytes()[offset:offset+4].hex()}
            v["comparisons"].append(row)
        write(dest / "comparison.json", v)
        result["variants"].append(v)
    write(directory / "case.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "target/prejit-baseline")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--input", type=Path, action="append")
    args = parser.parse_args()
    if args.jobs < 1: parser.error("--jobs must be positive")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    upstream = ROOT / "third_party/wasmtime"
    commit = subprocess.check_output(["git", "-C", upstream, "rev-parse", "HEAD"], text=True).strip()
    if commit != PIN: raise ValueError("wrong upstream revision")
    patch = subprocess.check_output(["git", "-C", upstream, "diff", "--", "cranelift/filetests"])
    (out / "upstream-instrumentation.patch").write_bytes(patch)
    stock = upstream / "cranelift/filetests/filetests/runtests"
    inputs = args.input or sorted(stock.rglob("*.clif"))
    inputs = [p.resolve() for p in inputs]
    for p in inputs: p.relative_to(stock.resolve())
    env = os.environ.copy()
    local = ROOT / "target/byte-agreement-tools"
    env["PATH"] = os.pathsep.join([str(ROOT / "rust/target/release"),str(local / "lean-4.34.1-linux/bin"),env.get("PATH", "")])
    binary = ROOT / "tools/prejit-export/target/debug/prejit-export"
    report = {"upstream_commit":commit,"target":TARGET,"actual_ci_execution":False,"execution_performed":False,
        "scope":"official runtime files, all declared AArch64 variants; stock compiler settings unchanged",
        "inventory":[str(p) for p in inputs],"cases":[],"progress":"running", "complete_equivalence":False,
        "instrumentation_sha256":hashlib.sha256(patch).hexdigest(),
        "exporter_lock_sha256":hashlib.sha256((ROOT / "tools/prejit-export/Cargo.lock").read_bytes()).hexdigest()}
    write(out / "results.json", report)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for case in pool.map(lambda p: one(p,out,env,binary), inputs):
            report["cases"].append(case)
            write(out / "results.json",report)
            print(f"{len(report['cases'])}/{len(inputs)} {case['case']}",flush=True)
    from collections import Counter
    files = Counter(c["status"] for c in report["cases"])
    variants = [v for c in report["cases"] for v in c["variants"]]
    rows = [r for v in variants for r in v["comparisons"]]
    counts = Counter(r["status"] for r in rows)
    report.update(progress="finished", totals={"files":len(inputs),"file_statuses":dict(files),"configurations":len(variants),
        "functions":len(rows),"function_statuses":dict(counts),"byte_matches":sum(r.get("bytes",{}).get("equal",False) for r in rows),
        "relocation_matches":sum(r.get("relocations_equal",False) for r in rows),
        "stock_excluded_configurations":sum(not v["eligible"] for v in variants),
        "reference_error_configurations":sum(v.get("error") is not None and v["eligible"] for v in variants),
        "paired_functions":sum(r["status"] in ("identical","different") for r in rows),
        "trap_metadata_matches":sum(r.get("trap_metadata",{}).get("equal",False) for r in rows),
        "alignment_matches":sum(r.get("alignment",{}).get("equal",False) for r in rows),
        "metadata_equivalence_verified":False,"settings_equivalence_verified":False})
    write(out / "results.json",report)
    summary = ["# Stock pre-JIT baseline", "", "Target: AArch64 Linux. Cross-compilation only; no CI execution claimed.",
        "Stock settings were not overridden. ELF packaging is not compared.", "", "```json",json.dumps(report["totals"],indent=2),"```", "",
        "Exact matches mean function bytes and relocations only. Settings parity, alignment, and full execution metadata equivalence are not established.",
        "Unsupported functions and reference failures remain coverage gaps."]
    (out / "summary.md").write_text("\n".join(summary)+"\n")
    print(json.dumps(report["totals"],indent=2))
    return 1 if counts.get("different") or counts.get("lean_missing") or counts.get("reference_missing") else 0


if __name__ == "__main__":
    raise SystemExit(main())
