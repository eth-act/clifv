#!/usr/bin/env python3
"""Compare a candidate compiler (native shim or extracted Lean) with stock filetest artifacts.

Stock artifacts come from tools/prejit-export (--all-stages). For each exported function the
candidate compiles the stock input `.clif` with the variant's settings; code bytes, relocations,
traps and alignment must equal the stock `write_code` output exactly. Rendering of relocation
targets and trap codes mirrors the pinned Rust `Display` impls (see render_* below).
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

EXTRACT = Path(__file__).resolve().parent.parent
ROOT = EXTRACT.parent
sys.path.insert(0, str(ROOT / "scripts"))
_spec = importlib.util.spec_from_file_location("stock_compiler_compare", ROOT / "scripts/stock-compiler-compare.py")
scc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(scc)
artifacts, SUITE, TARGET = scc.artifacts, scc.SUITE, scc.TARGET

PREJIT = ROOT / "tools/prejit-export/target/debug/prejit-export"
CANDIDATES = {
    "native": EXTRACT / "rust/target/release/clifv-extract-native",
    "lean": EXTRACT / "lean/.lake/build/bin/clifv-extract-lean",
}
TIMEOUT = 600

# cranelift/codegen/src/ir/trapcode.rs: reserved codes are u8::MAX - 5 + 1 + k.
TRAP_NAMES = {251: "stk_ovf", 252: "int_ovf", 253: "heap_oob", 254: "int_divz", 255: "bad_toint"}


# cranelift/module/src/lib.rs `default_libcall_names`, used by the stock run-stage export.
LIBCALL_NAMES = {"Probestack": "__cranelift_probestack", "CeilF32": "ceilf", "CeilF64": "ceil",
    "FloorF32": "floorf", "FloorF64": "floor", "TruncF32": "truncf", "TruncF64": "trunc",
    "NearestF32": "nearbyintf", "NearestF64": "nearbyint", "FmaF32": "fmaf", "FmaF64": "fma",
    "Memcpy": "memcpy", "Memset": "memset", "Memmove": "memmove", "Memcmp": "memcmp",
    "ElfTlsGetAddr": "__tls_get_addr", "ElfTlsGetOffset": "__tls_get_offset",
    "X86Pshufb": "__cranelift_x86_pshufb"}

# The stock export prints its input with `Function::to_string`, which is not faithful for
# dynamic vector types (declarations dropped, `types::…` debug names) and symbol global values
# (`userextname<ref>` instead of the user name). Those inputs are taken from the source file.
LOSSY_PRINT = re.compile(r"\buserextname\d|\btypes::|\bdt\d+\b")


def source_function(rel, key, name):
    """Text of the key-th `function` block of the suite file, if its name is `name`."""
    lines = (SUITE / rel).read_text().splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if line.startswith("function ")]
    if key >= len(starts) or not lines[starts[key]].startswith(f"function {name}("):
        return None
    end = next((j for j in range(starts[key], len(lines)) if lines[j].rstrip() == "}"), None)
    return None if end is None else "".join(lines[starts[key]:end + 1])


def render_trap(code):
    """`impl Display for TrapCode`."""
    return TRAP_NAMES.get(code, f"user{code}")


def render_func_name(name):
    """`impl Display for UserFuncName`: `u{ns}:{index}` or `%{testcase}`."""
    if "user" in name:
        ns, index = name["user"]
        return f"u{ns}:{index}"
    return "%" + name["testcase"]


def render_target(target, func_name, addend, stage):
    """`write_code`: ExternalName::display(Some(&func.params)) or the function's own name for
    `Func(offset)` with addend + offset; then `trim_start_matches('%')`. The run stage
    (function_runner `export_prejit`) names libcalls with `cranelift_module::default_libcall_names`."""
    if "func_offset" in target:
        name, addend = render_func_name(func_name), addend + target["func_offset"]
    elif "user" in target:
        ns, index = target["user"]
        name = f"u{ns}:{index}"
    elif "testcase" in target:
        name = "%" + target["testcase"]
    elif "libcall" in target:
        name = LIBCALL_NAMES[target["libcall"]] if stage == "run" else "%" + target["libcall"]
    elif "known_symbol" in target:
        name = "%" + target["known_symbol"]
    else:
        raise ValueError(f"unknown reloc target {target}")
    return name.lstrip("%"), addend


def render(result, stage):
    relocs = []
    for r in result["relocs"]:
        target, addend = render_target(r["target"], result["func_name"], r["addend"], stage)
        relocs.append({"offset": r["offset"], "kind": r["kind"], "target": target, "addend": addend})
    traps = [{"offset": t["offset"], "code": render_trap(t["code"])} for t in result["traps"]]
    return relocs, traps


def opt_level(variant):
    return next((f["value"] for f in variant["flags"] if f["name"] == "opt_level"), None)


def run_candidate(binary, request_path, result_path):
    try:
        proc = subprocess.run([str(binary), str(request_path), str(result_path)],
                              capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    result_path.with_suffix(".stderr").write_bytes(proc.stderr)
    if proc.returncode != 0:
        return None, f"exit {proc.returncode}"
    try:
        return json.loads(result_path.read_text()), None
    except (OSError, ValueError) as e:
        return None, f"invalid result: {e}"


def compare(result, json_path, meta, stage):
    relocs, traps = render(result, stage)
    checks = [
        ("code", bytes.fromhex(result["code_hex"]) == json_path.with_suffix(".bin").read_bytes()),
        ("relocations", relocs == meta["relocations"]),
        ("traps", traps == meta["traps"]),
        ("alignment", result["alignment"] == meta["alignment"]),
    ]
    return next((field for field, ok in checks if not ok), None)


def one_file(rel, args, targets):
    base = args.out / "files" / rel
    stock = base / "stock"
    rows = []
    if not (stock / "manifest.json").exists():
        stock.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([str(PREJIT), str(SUITE / rel), str(stock), TARGET, "--all-stages"],
                       capture_output=True, timeout=TIMEOUT)
    try:
        manifest = json.loads((stock / "manifest.json").read_text())
    except (OSError, ValueError):
        return [{"file": rel, "status": "stock_reference_error", "field": "manifest"}]
    for variant in manifest["variants"]:
        if variant["status"] != "exported":
            continue
        vdir = stock / f"variant-{variant['index']}"
        try:
            metas = artifacts(vdir, variant)
        except ValueError as e:
            rows.append({"file": rel, "variant": variant["index"], "status": "stock_reference_error", "field": str(e)})
            continue
        for key, (json_path, meta) in sorted(metas.items()):
            name = meta["name"]
            row = {"file": rel, "variant": variant["index"], "name": name, "key": key, "target": variant["target"]}
            rows.append(row)
            if json_path.with_name(json_path.name.removesuffix(".json") + ".rejection.json").exists():
                row["status"] = "stock_reference_error"
                continue
            if args.opt_levels == "none" and opt_level(variant) != "none":
                row["status"] = "out_of_scope_opt_level"
                continue
            spec = targets.get(variant["target"])
            if spec is None:
                row["status"] = "unmapped_target"
                continue
            work = base / f"variant-{variant['index']}"
            work.mkdir(parents=True, exist_ok=True)
            stem = json_path.name.removesuffix(".json")
            clif_path = json_path.with_suffix(".clif")
            if LOSSY_PRINT.search(clif_path.read_text()):
                text = source_function(rel, key, name)
                if text is None:
                    row.update(status="stock_reference_error", field="lossy_input_without_source")
                    continue
                clif_path = work / f"{stem}.source.clif"
                clif_path.write_text(text)
                row["input"] = "source"
            request = {"schema": 1, "clif_path": str(clif_path), "target": variant["target"],
                       "target_spec": spec, "flags": variant["flags"], "isa_flags": variant["isa_flags"]}
            request_path = work / f"{stem}.request.json"
            request_path.write_text(json.dumps(request))
            result_path = work / f"{stem}.{args.candidate}.result.json"
            result, error = run_candidate(CANDIDATES[args.candidate], request_path, result_path)
            if args.candidate == "lean":
                native_path = args.out / "native-results" / rel / f"variant-{variant['index']}" / f"{stem}.result.json"
                native_path.parent.mkdir(parents=True, exist_ok=True)
                run_candidate(CANDIDATES["native"], request_path, native_path)
            if result is None:
                row.update(status="candidate_error", field=error)
            elif result.get("status") == "rejected":
                row.update(status="candidate_rejected", field=result.get("stage"))
            elif result.get("status") != "compiled":
                row.update(status="candidate_error", field=result.get("reason", result.get("status")))
            else:
                field = compare(result, json_path, meta, variant["stage"])
                row.update(status="different" if field else "identical", field=field)
            if args.candidate == "lean" and result_path.exists():
                native = native_path.read_bytes() if native_path.exists() else None
                if native != result_path.read_bytes():
                    row.update(status="differs_from_native", field=row.get("field") or "result_json")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidate", choices=["native", "lean"], required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--input", action="append", default=[])
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--opt-levels", choices=["none", "all"], default="none")
    args = ap.parse_args()
    if not PREJIT.exists():
        subprocess.run(["bash", str(ROOT / "scripts/prejit-export-build.sh")], check=True)
    if not CANDIDATES[args.candidate].exists():
        sys.exit(f"missing candidate binary {CANDIDATES[args.candidate]}")
    targets = {t["target"]: t["spec"] for t in json.loads((EXTRACT / "targets.json").read_text())}
    inputs = args.input or sorted(str(p.relative_to(SUITE)) for p in SUITE.rglob("*.clif"))
    args.out.mkdir(parents=True, exist_ok=True)
    rows = []
    with ThreadPoolExecutor(args.jobs) as pool:
        for file_rows in pool.map(lambda rel: one_file(rel, args, targets), inputs):
            rows.extend(file_rows)
    (args.out / "results.json").write_text(json.dumps(rows, indent=1))
    summary = {"counts": dict(Counter(r["status"] for r in rows)),
               "unmapped_targets": sorted({r["target"] for r in rows if r["status"] == "unmapped_target"}),
               "fields": dict(Counter(f'{r["status"]}:{r.get("field")}' for r in rows
                                      if r["status"] not in ("identical", "out_of_scope_opt_level")))}
    (args.out / "summary.json").write_text(json.dumps(summary, indent=1))
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
