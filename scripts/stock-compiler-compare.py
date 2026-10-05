#!/usr/bin/env python3
"""Compare unmodified stock filetest compilation requests with Lean, fail closed.

Inventory is the entire pinned official .clif suite. compile and run are separate
stock stages, not an invented configuration sweep. There is no binary normalization.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import traceback
import tomllib

from byte_compare import ELF, digest

SPEC = importlib.util.spec_from_file_location("prejit", Path(__file__).with_name("prejit-baseline.py"))
PREJIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PREJIT)
ROOT, PIN, TARGET = PREJIT.ROOT, PREJIT.PIN, PREJIT.TARGET
# Resolved: agent worktrees link third_party/wasmtime (scripts/agent-worktree.sh).
SUITE = (ROOT / "third_party/wasmtime/cranelift/filetests/filetests").resolve()
write, command, comparison = PREJIT.write, PREJIT.command, PREJIT.comparison

ELF_RELOC_TYPES = {"Arm64Call":283,"Aarch64AdrPrelPgHi21":275,"Aarch64AddAbsLo12Nc":277,
    "Aarch64AdrGotPage21":311,"Aarch64Ld64GotLo12Nc":312,
    "Aarch64TlsDescAdrPage21":562,"Aarch64TlsDescLd64Lo12":563,
    "Aarch64TlsDescAddLo12":564,"Aarch64TlsDescCall":569}


def request_for(variant, source):
    return {"schema": 1, "target": variant["target"], "flags": variant["flags"],
            "isa_flags": variant["isa_flags"], "input_sha256": digest(source),
            "stage": variant["stage"], "isa_index": variant["isa_index"],
            "command_index": variant["command_index"]}


def verify_receipt(request, receipt, source):
    if digest(source) != request["input_sha256"]:
        return "shared compiler input changed"
    if receipt.get("schema") != 1 or receipt.get("request") != request:
        return "Lean configuration receipt does not echo the exact stock request"
    if not receipt.get("configuration_accepted"):
        return receipt.get("error") or "unsupported stock configuration"
    return None


def function_rejections(receipt):
    """Functions that lean-backend rejected for a setting, written after compilation."""
    rejections = receipt.get("function_rejections")
    if not isinstance(rejections, dict) or not all(isinstance(v, str) for v in rejections.values()):
        return None
    return rejections


def artifacts(directory):
    result = {}
    for path in directory.glob("*.json"):
        value = json.loads(path.read_text())
        if isinstance(value, dict) and "relocations" in value and "name" in value:
            if value["name"] in result:
                raise ValueError("duplicate stock function identity")
            result[value["name"]] = (path, value)
    return result


def repeat_check(first, second):
    """Compare raw stock payloads/metadata, not output paths or timestamps."""
    a, b = artifacts(first), artifacts(second)
    if a.keys() != b.keys():
        return False
    return all(meta == b[name][1] and path.with_suffix(".bin").read_bytes() ==
               b[name][0].with_suffix(".bin").read_bytes() for name, (path, meta) in a.items())


def check_pinned_dependencies(upstream, exporter_lock):
    stock = tomllib.loads((upstream / "Cargo.lock").read_text())
    ours = tomllib.loads(exporter_lock.read_text())
    def identity(package):
        return package["name"],package["version"],package.get("source")
    known = {identity(p) for p in stock["package"]}
    unexpected = [identity(p) for p in ours["package"] if p["name"] != "prejit-export" and identity(p) not in known]
    if unexpected: raise ValueError(f"exporter dependencies differ from stock lockfile: {unexpected}")
    return {"all_exporter_dependencies_match_stock_lockfile":True,
            "upstream_lock_sha256":digest((upstream/"Cargo.lock").read_bytes()),
            "exporter_lock_sha256":digest(exporter_lock.read_bytes())}


def compare_function(name, artifact, lean_dir, config_verified, repeatable):
    path, stock = artifact
    lean_name = name.removeprefix("%")
    if not re.fullmatch(r"[A-Za-z0-9_.$:-]+", lean_name):
        return {"name": name, "status": "unsupported_symbol_identity"}
    code_path = lean_dir / "dump" / (lean_name + ".bin")
    if not code_path.exists():
        return {"name": name, "status": "lean_unsupported", "reason": "see lean.stderr and traps.json"}
    code = code_path.read_bytes()
    relocs = json.loads(code_path.with_name(lean_name + ".relocs.json").read_text())
    traps = json.loads(code_path.with_name(lean_name + ".traps.json").read_text())
    metadata = json.loads(code_path.with_name(lean_name + ".metadata.json").read_text())
    row = {"name": name, **comparison(path.with_suffix(".bin").read_bytes(), code, stock["relocations"], relocs)}
    row["alignment_equal"] = stock["alignment"] == metadata["alignment"]
    row["traps_equal"] = stock["traps"] == traps
    row["traps"] = {"stock": stock["traps"], "lean": traps}
    row["alignment"] = {"stock": stock["alignment"], "lean": metadata["alignment"]}
    elf = ELF(lean_dir / "program.o")
    symbol, object_code = elf.function(lean_name)
    row["lean_dump_matches_object_bytes"] = object_code == code
    row["lean_object_alignment_valid"] = elf.section(symbol["section"])["alignment"] >= metadata["alignment"] and symbol["value"] % metadata["alignment"] == 0
    object_relocs = elf.function_relocations(symbol,{})
    dumped_relocs = sorted([{"offset":r["offset"],"type":ELF_RELOC_TYPES.get(r["kind"]),
        "target":r["target"].removeprefix("%"),"addend":r["addend"]} for r in relocs],
        key=lambda r:(r["offset"],r["type"] or 0,r["target"],r["addend"]))
    row["lean_dump_matches_object_relocations"] = dumped_relocs == object_relocs
    row["settings_contract_verified"] = config_verified
    row["stock_artifact_repeatable"] = repeatable
    # The shared payload verdict includes all comparable fields, with unsupported
    # execution metadata reported separately. Unknown fields are NEVER equal.
    row["exact_code_artifact"] = (row["exact_code_and_relocations"] and row["alignment_equal"]
                                  and row["traps_equal"] and object_code == code
                                  and row["lean_dump_matches_object_relocations"]
                                  and row["lean_object_alignment_valid"]
                                  and config_verified and repeatable)
    unwind_equal = stock["unwind"] == "None" and metadata["unwind_disabled"] and not any(
        s["name"] == ".eh_frame" for s in elf.sections)
    stack_equal = stock["stack_maps"] == "[]" and metadata["stack_maps"] == []
    # There is no Lean export of Cranelift's exception table format yet. Absence
    # of landing pads does not prove absence/equality of its regular-call records.
    row["execution_metadata"] = {"unwind_equal": unwind_equal if metadata["unwind_disabled"] else None,
        "stack_maps_equal": stack_equal if stock["stack_maps"] == "[]" else None,
        "exception_metadata_equal": None, "stock_unwind": stock["unwind"],
        "stock_exception_call_sites": stock["exception_call_sites"],
        "stock_exception_table_bytes": stock["exception_table_bytes"], "stock_stack_maps": stock["stack_maps"],
        "full_metadata_equivalence_verified": False}
    row["full_artifact_equivalence_verified"] = False
    row["status"] = "identical_code_artifact" if row["exact_code_artifact"] else "different_code_artifact"
    return row


def compile_lean(variant, source, dest, env):
    dest.mkdir(parents=True)
    input_path = dest / "input.clif"
    input_path.write_bytes(source)
    request = request_for(variant, source)
    config = dest / "stock-config.json"
    receipt_path = dest / "configuration-receipt.json"
    write(config, request)
    lean = dest / "lean"
    lean.mkdir()
    run = command([ROOT / ".lake/build/bin/lean-backend", input_path, lean / "program.o",
        "--stock-config", config, "--config-receipt", receipt_path,
        "--dump", lean / "dump", "--traps", lean / "traps.json"], dest, "lean", env)
    receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {}
    error = verify_receipt(request, receipt, input_path.read_bytes())
    rejections = function_rejections(receipt)
    # A finished compilation without the per-function list is a harness failure, not a gap.
    return lean, {"command":run,"request":request,"receipt":receipt,"contract_error":error,
                  "function_rejections":rejections or {},
                  "contract_verified":error is None and run["exit"] == 0 and rejections is not None}


def one(path, out, env, binary, repeat):
    relative = str(path.relative_to(SUITE))
    dest = out / "files" / relative.removesuffix(".clif")
    dest.mkdir(parents=True)
    original = path.read_bytes()
    (dest / "original.clif").write_bytes(original)
    row = {"test":relative,"source_sha256":digest(original),"category":relative.split('/')[0],"variants":[]}
    # Even malformed parser tests must remain in the official command inventory.
    row["declared_commands"] = re.findall(r"^test\s+([^\n;]+)", original.decode(), re.M)
    reference = dest / "stock"
    row["export_command"] = command([binary,path,reference,TARGET,"--all-stages"],dest,"stock",env)
    if not (reference / "manifest.json").exists():
        row["status"] = "reference_export_failed"
        write(dest / "result.json", row)
        return row
    manifest = json.loads((reference / "manifest.json").read_text())
    row["manifest"] = manifest
    if manifest.get("parse_error"):
        row.update(status="stock_parser_warning_skip" if manifest.get("parse_error_is_warning") else "stock_parser_error",reason=manifest["parse_error"])
    elif manifest.get("missing_required_isa"):
        row["status"] = "stock_missing_required_isa"
    elif not any(c.split()[0] in ("compile","run","unwind") for c in row["declared_commands"]):
        row["status"] = "non_binary_test"
    elif not manifest["variants"]:
        row["status"] = "no_lean_target"
    else:
        row["status"] = "binary_test"
    second = dest / "stock-repeat"
    if repeat and manifest["variants"]:
        row["repeat_command"] = command([binary,path,second,TARGET,"--all-stages"],dest,"stock-repeat",env)
    for variant in manifest["variants"]:
        v = {**variant, "functions_compared":[], "lean_compilations":[]}
        stock_dir = reference / f"variant-{variant['index']}"
        v["reference_repeat_verified"] = bool(repeat and row.get("repeat_command",{}).get("exit") == 0
            and repeat_check(stock_dir, second / stock_dir.name))
        if (stock_dir / "assertions.json").exists():
            v["stock_compile_assertions"] = json.loads((stock_dir / "assertions.json").read_text())
        v["stock_runtime_assertions_executed"] = False
        metas = artifacts(stock_dir)
        sources = {}
        for source in stock_dir.glob("*.clif"):
            if source.name.endswith(".lean.clif"): continue
            name = re.search(r"^function\s+(\S+)\(", source.read_text(),re.M)
            if name and name[1] in variant["functions"]:
                sources[name[1]] = source
        v["prepared_functions"] = list(sources)
        rejected = {}
        for rejection in stock_dir.glob("*.rejection.json"):
            data = json.loads(rejection.read_text())
            rejected[data["name"]] = data
        v["expected_stock_rejections"] = list(rejected.values())
        # compile: independent functions, just like TestCompile::run; run:
        # compile the whole prepared module, just like TestFileCompiler.
        groups = [[n] for n in variant["functions"] if n in sources and n in metas] if variant["stage"] == "compile" else [list(sources)]
        compiled = {}
        for index, names in enumerate(groups):
            if not names: continue
            effective = b"\n\n".join(sources[n].read_bytes() for n in names)
            adapted = b"\n\n".join(sources[n].with_name(sources[n].stem + ".lean.clif").read_bytes() for n in names)
            group_dir = dest / f"variant-{variant['index']}" / f"compilation-{index}"
            lean, contract = compile_lean(variant, adapted, group_dir, env)
            (group_dir / "stock-effective.clif").write_bytes(effective)
            contract["stock_effective_input_sha256"] = digest(effective)
            contract["input_adaptation"] = "inline signature references only; stock-reader IR identity checked by exporter"
            contract["functions"] = names
            v["lean_compilations"].append(contract)
            for name in names: compiled[name] = (lean, contract)
        for name in variant["functions"]:
            if name in rejected:
                r = {"name":name,"status":"expected_stock_rejection_no_binary","lean_rejection_compared":False}
            elif not variant["eligible"]:
                r = {"name":name,"status":"stock_excluded", "reason":variant["error"]}
            elif name not in metas:
                r = {"name":name,"status":"reference_missing", "reason":variant["error"]}
            elif name not in compiled:
                r = {"name":name,"status":"shared_input_missing"}
            else:
                lean, contract = compiled[name]
                if contract["contract_error"]:
                    r = {"name":name,"status":"unsupported_configuration","reason":contract["contract_error"]}
                elif not contract["contract_verified"]:
                    r = {"name":name,"status":"lean_compilation_failed","reason":contract["command"]["exit"]}
                elif name.removeprefix("%") in contract["function_rejections"]:
                    r = {"name":name,"status":"unsupported_configuration",
                         "reason":contract["function_rejections"][name.removeprefix("%")]}
                else:
                    r = compare_function(name, metas[name], lean, True, v["reference_repeat_verified"])
            v["functions_compared"].append(r)
        v["all_test_function_code_artifacts_identical"] = bool(v["functions_compared"]) and all(
            r["status"] == "identical_code_artifact" for r in v["functions_compared"])
        row["variants"].append(v)
    row["all_declared_aarch64_code_artifacts_identical"] = bool(row["variants"]) and all(
        v["all_test_function_code_artifacts_identical"] for v in row["variants"])
    row["original_source_unchanged"] = original == path.read_bytes()
    write(dest / "result.json",row)
    return row


def summarize(report):
    cases = report["tests"]
    variants = [v for c in cases for v in c["variants"]]
    rows = [r for v in variants for r in v["functions_compared"]]
    return {"official_test_files":report["official_test_files"],"inventoried_test_files":len(cases),
        "files_by_category":dict(Counter(c["category"] for c in cases)),
        "file_statuses":dict(Counter(c["status"] for c in cases)),
        "files_with_lean_compilation_attempts":sum(any(v["lean_compilations"] for v in c["variants"]) for c in cases),
        "files_with_compared_function_outputs":sum(any("bytes" in r for v in c["variants"] for r in v["functions_compared"]) for c in cases),
        "files_all_aarch64_code_artifacts_identical":sum(c.get("all_declared_aarch64_code_artifacts_identical",False) for c in cases),
        "stock_binary_stages_by_command":dict(Counter(v["stage"] for v in variants)),
        "declared_stock_commands":dict(Counter(command.split()[0] for c in cases for command in c.get("declared_commands",[]))),
        "accepted_lean_configuration_requests":sum(c["contract_verified"] for v in variants for c in v["lean_compilations"]),
        "unsupported_configuration_reasons":dict(Counter(r["reason"] for r in rows if r["status"]=="unsupported_configuration")),
        "test_function_compilations":len(rows),"function_statuses":dict(Counter(r["status"] for r in rows)),
        "distinct_test_function_names":len({(c["test"],r["name"]) for c in cases for v in c["variants"] for r in v["functions_compared"]}),
        "byte_and_relocation_matches_under_accepted_settings":sum(r.get("exact_code_and_relocations",False) for r in rows),
        "exact_code_artifacts":sum(r.get("exact_code_artifact",False) for r in rows),
        "full_artifact_equivalence_verified":False,
        "failed_stock_compile_assertions":sum(not a["passed"] for v in variants for a in v.get("stock_compile_assertions",[])),
        "nonrepeatable_reference_stages":sum(not v["reference_repeat_verified"] for v in variants),
        "source_files_modified":sum(not c.get("original_source_unchanged",True) for c in cases)}


def safe_one(path, out, env, binary):
    try:
        return one(path,out,env,binary,True)
    except Exception as error:
        relative = str(path.relative_to(SUITE))
        result = {"test":relative,"category":relative.split('/')[0],"status":"harness_error",
                  "variants":[],"error":str(error),"traceback":traceback.format_exc()}
        write(out / "files" / relative.removesuffix(".clif") / "harness-error.json",result)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,default=ROOT / "target/stock-compiler-comparison")
    parser.add_argument("--input",type=Path,action="append")
    parser.add_argument("--jobs",type=int,default=2)
    args = parser.parse_args()
    if args.jobs < 1: parser.error("--jobs must be positive")
    if os.environ.get("BLESS") is not None: parser.error("BLESS must be unset")
    out = args.out.resolve()
    out.mkdir(parents=True,exist_ok=False)
    upstream = ROOT / "third_party/wasmtime"
    commit = subprocess.check_output(["git","-C",upstream,"rev-parse","HEAD"],text=True).strip()
    if commit != PIN: raise ValueError("wrong stock revision")
    patch = subprocess.check_output(["git","-C",upstream,"diff","--","cranelift/filetests"])
    checked_patch = ROOT / "scripts/patches/prejit-export.patch"
    subprocess.run(["git","-C",upstream,"apply","--reverse","--check",checked_patch],check=True,capture_output=True)
    (out / "upstream-instrumentation.patch").write_bytes(checked_patch.read_bytes())
    (out / "upstream-tracked-diff.patch").write_bytes(patch)
    helper = upstream / "cranelift/filetests/src/artifact_export.rs"
    (out / "artifact_export.rs").write_bytes(helper.read_bytes())
    all_inputs = sorted(SUITE.rglob("*.clif"))
    inputs = [p.resolve() for p in (args.input or all_inputs)]
    for p in inputs:
        p.relative_to(SUITE)
        if not p.is_file(): raise ValueError(f"missing test file: {p}")
    env = os.environ.copy()
    env["PATH"] = os.pathsep.join([str(ROOT / "rust/target/release"),
        str(ROOT / "target/byte-agreement-tools/lean-4.34.1-linux/bin"),env.get("PATH","")])
    binary = ROOT / "tools/prejit-export/target/debug/prejit-export"
    sources = [ROOT / "FVTest/Backend/StockConfig.lean", ROOT / "FVTest/Backend/Main.lean",
               ROOT / "tools/prejit-export/src/main.rs", ROOT / "tools/prejit-export/Cargo.lock", checked_patch, Path(__file__)]
    dependencies = check_pinned_dependencies(upstream,ROOT/"tools/prejit-export/Cargo.lock")
    lean_sources = sorted([*ROOT.joinpath("FV").rglob("*.lean"),*ROOT.joinpath("FVTest").rglob("*.lean")])
    lean_tree = hashlib.sha256()
    for path in lean_sources:
        lean_tree.update(str(path.relative_to(ROOT)).encode()+b"\0"+path.read_bytes()+b"\0")
    report = {"schema":1,"upstream_commit":commit,"official_test_files":len(all_inputs),"target":TARGET,
        "inventory":[{"test":str(p.relative_to(SUITE)),"sha256":digest(p.read_bytes())} for p in all_inputs],
        "source_hashes":{str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in sources},
        "lean_source_tree_sha256":lean_tree.hexdigest(),"dependency_provenance":dependencies,
        "binary_hashes":{str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in [binary, ROOT/".lake/build/bin/lean-backend",ROOT/"rust/target/release/lean-regalloc"]},
        "actual_ci_execution":False,"execution_performed":False,"configuration_overrides":[],"binary_normalization":False,
        "progress":"running","tests":[],"full_artifact_equivalence_verified":False}
    write(out / "progress.json", {"completed":0,"total":len(inputs)})
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for case in pool.map(lambda p:safe_one(p,out,env,binary),inputs):
            report["tests"].append(case)
            write(out / "progress.json",{"completed":len(report["tests"]),"total":len(inputs),"last_test":case["test"]})
            print(f"{len(report['tests'])}/{len(inputs)} {case['test']}",flush=True)
    report.update(progress="finished",totals=summarize(report))
    write(out / "results.json",report)
    (out / "summary.md").write_text("# Stock/Lean compiler comparison\n\nAll official filetests inventoried; unchanged stock settings.\n"
        "AArch64 cross-host compilation, not an actual CI execution.\nNo stripping, masking, or machine-byte normalization.\n\n```json\n"
        + json.dumps(report["totals"],indent=2) + "\n```\n\n"
        "Code-artifact equality means identical code bytes, relocations, alignment and traps under an accepted settings contract.\n"
        "Full artifact equality additionally requires unwind, stack maps and exception metadata; unknown metadata is not a pass.\n"
        "Functions repeat when a stock test declares multiple targets/settings or binary-producing commands.\n"
        "Non-binary tests, foreign architectures, unsupported settings and missing outputs are explicit coverage categories.\n")
    print(json.dumps(report["totals"],indent=2))
    # Strict mode cannot report suite success with coverage gaps or unknown metadata.
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
