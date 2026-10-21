#!/usr/bin/env python3
"""Execute StockMixedRuntime's exported Lean objects and compare Cranelift.

First run StockMixedRuntime.lean with STOCK_MIXED_NATIVE_OUT set to a fresh
artifact directory. Run this script through scripts/memcap.sh; native tools run
sequentially and lld uses one thread. CLIF_NATIVE_QEMU and CLIF_NATIVE_LLD follow
the existing clif-native tool convention.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import os
import re
import shlex
import shutil
import subprocess


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signed(value, bits):
    value %= 1 << bits
    return value if value < 1 << (bits - 1) else value - (1 << bits)


def run_commands(bits, kind="mixed"):
    low, high = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
    vectors = [
        [0, 5, 2, 11, 22, 33, 44, 55, 7],
        [1, 5, 2, 11, 22, 33, 44, 55, 7],
        [-1, -1, 1, 11, 22, 33, 44, 55, 1],
        [0, low, 1, 11, 22, 33, 44, 55, -1],
        [1, high, -1, 11, 22, 33, 44, 55, 1],
        [2, 0, high, 11, 22, 33, 44, 55, low],
        [1, low, low, 11, 22, 33, 44, 55, low],
    ]
    cases = []
    for args in vectors:
        selected = args[1] + args[8] if args[0] else args[1]
        if kind == "scalar":
            mask = (1 << bits) - 1
            constant = 0x123456789abcdef & mask
            band = ((args[1] + constant) & args[8]) & mask
            logical = ((band ^ (args[2] & mask)) | constant) & mask
            chosen = logical if args[0] else band
            cases.append(("stock_scalar_ni", args, signed(chosen - args[2] + 4097, bits)))
            prior_band = (args[1] & args[8]) & mask
            prior_logical = ((prior_band ^ (args[2] & mask)) | (args[1] & mask)) & mask
            cases.append(("retained_logical", args, signed((prior_logical if args[0] else prior_band) - args[2], bits)))
            cases.append(("retained_mixed", args, signed(selected - args[2], bits)))
        elif kind == "logical":
            mask = (1 << bits) - 1
            band = (args[1] & args[8]) & mask
            logical = ((band ^ (args[2] & mask)) | (args[1] & mask)) & mask
            chosen = logical if args[0] else band
            cases.append(("stock_logical_ni", args, signed(chosen - args[2], bits)))
            cases.append(("retained_mixed", args, signed(selected - args[2], bits)))
        else:
            cases.append(("stock_mixed_ni", args, signed(selected - args[2], bits)))
        cases.append(("retained_arithmetic", args, signed(args[0] + args[8] - args[1], bits)))
    for a, b in [(0, 0), (-1, 1), (high, 1), (low, low)]:
        cases.append(("retained_scalar", [a, b], signed(a + b, bits)))
    for value in [0, -1, (1 << 63) - 1]:
        cases.append(("retained_prologue", [value], value))
    for value in [0, -1, (1 << 31) - 1, -(1 << 31)]:
        cases.append(("retained_d0", [value], value))
    if kind == "scalar":
        for a, b in [(0, 7), (-1, 9), ((1 << 63) - 1, 3)]:
            cases.append(("retained_legacy", [a, b], signed(a * b, 64)))
    else:
        cases.append(("retained_legacy", [], 7))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("--native-bin", type=Path, default=Path("rust/target/release/clif-native"))
    parser.add_argument("--class", dest="kind", choices=["mixed", "logical", "scalar"], default="mixed")
    options = parser.parse_args()
    root = options.artifacts.resolve()
    native = options.native_bin.resolve()
    assert native.is_file(), native
    env = dict(os.environ)
    lld = env.get("CLIF_NATIVE_LLD") or shutil.which("rust-lld")
    assert lld, "Set CLIF_NATIVE_LLD to the installed rust-lld executable"
    wrapper = root / "lld-one-thread.sh"
    wrapper.write_text("#!/bin/sh\nexec " + shlex.quote(lld) + ' "$@" --threads=1\n')
    wrapper.chmod(0o700)
    env.update(CLIF_NATIVE_LLD=str(wrapper), RAYON_NUM_THREADS="1", OMP_NUM_THREADS="1")
    pattern = re.compile(r"^(lean|regalloc2)-Backend\.Stock\.D0\.Configuration\.((?:default|systemV|fast)I(32|64))-(plain|cleanup)$")
    expected_grid = set(itertools.product(
        ["lean", "regalloc2"],
        [a + b for a in ["default", "systemV", "fast"] for b in ["I32", "I64"]],
        ["plain", "cleanup"],
    ))
    seen, records = set(), []
    reference_cache = {}
    reference_executions = 0
    for obj in sorted(root.glob("*.o")):
        match = pattern.fullmatch(obj.stem)
        assert match, obj.name
        allocator, config, width, cleanup = match.groups()
        key = allocator, config, cleanup
        assert key not in seen, key
        seen.add(key)
        table, original = obj.with_suffix(".json"), obj.with_suffix(".clif")
        names = {f["name"] for f in json.loads(table.read_text())["functions"]}
        wanted = {"stock_mixed_ni", "retained_arithmetic", "retained_scalar",
                  "retained_prologue", "retained_d0", "retained_legacy"}
        if options.kind == "scalar":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_scalar_ni", "retained_logical", "retained_mixed"}
        elif options.kind == "logical":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_logical_ni", "retained_mixed"}
        assert names == wanted, names
        cases = run_commands(int(width), options.kind)
        attached = set()
        def add_commands(match):
            name = match.group(1)
            attached.add(name)
            commands = "\n".join(
                f"; run: %{name}({', '.join(map(str, args))}) == {value}"
                for function, args, value in cases if function == name
            )
            return match.group(0) + "\n" + commands + "\n"
        source = root / (obj.stem + "-runs.clif")
        text = re.sub(r"(?ms)^function %([A-Za-z_][A-Za-z_0-9]*)\b[^\n]*\{.*?^\}",
                      add_commands, original.read_text())
        assert attached == names, (attached, names)
        source.write_text(text)
        streams = {}
        reference_reused = False
        for engine, extra in [
            ("lean", ["--functions-obj", str(obj), "--functions-table", str(table)]),
            ("cranelift", []),
        ]:
            log = root / (obj.stem + "-" + engine + ".jsonl")
            error = root / (obj.stem + "-" + engine + ".stderr")
            reference_key = sha(source)
            if engine == "cranelift" and reference_key in reference_cache:
                log.write_bytes(reference_cache[reference_key].read_bytes())
                error.write_text("Reused identical source/reference input from this run.\n")
                reference_reused = True
            else:
                with log.open("w") as out, error.open("w") as err:
                    result = subprocess.run([str(native), str(source), *extra], env=env,
                                            stdout=out, stderr=err)
                assert result.returncode == 0, (engine, source, error.read_text()[-3000:])
                if engine == "cranelift":
                    reference_cache[reference_key] = log
                    reference_executions += len(cases)
            rows = [json.loads(line) for line in log.read_text().splitlines() if line.strip()]
            assert len(rows) == len(cases), (engine, source, len(rows), len(cases))
            for row in rows:
                assert "file_error" not in row and row.get("expected"), row
                assert row["expected"]["cmp"] == "==", row
                assert row["actual"].get("returned") == row["expected"]["values"], row
            streams[engine] = rows
        assert [r["actual"] for r in streams["lean"]] == [r["actual"] for r in streams["cranelift"]]
        records.append({"allocator": allocator, "configuration": config, "cleanup": cleanup,
                        "runs": len(cases), "cranelift_reference_reused": reference_reused, "object_sha256": sha(obj),
                        "table_sha256": sha(table), "original_source_sha256": sha(original),
                        "executed_source_sha256": sha(source),
                        "lean_records_sha256": sha(root / (obj.stem + "-lean.jsonl")),
                        "cranelift_records_sha256": sha(root / (obj.stem + "-cranelift.jsonl"))})
        print(f"{allocator} {config} {cleanup}: {len(cases)} Lean byte executions agree with Cranelift", flush=True)
    assert seen == expected_grid, ("missing", sorted(expected_grid - seen), "extra", sorted(seen - expected_grid))
    result = {"state": "passed", "actual_lean_encoded_objects": len(records),
              "lean_byte_executions": sum(r["runs"] for r in records),
              "cranelift_reference_executions": reference_executions,
              "reference_cases_compared": sum(r["runs"] for r in records),
              "failures": 0, "disagreements": 0, "native_binary_sha256": sha(native),
              "records": records,
              "limits": "Fixed native integration grid; normal proof and full current activation gates remain required."}
    (root / "native-receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "records"}), flush=True)


if __name__ == "__main__":
    main()
