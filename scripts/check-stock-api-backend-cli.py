#!/usr/bin/env python3
"""Compare ordinary lean-backend CLI output with a passed native API matrix.

The matrix comes from check-stock-mixed-native.py. This checks compiler CLI
routing as well as the separately tested runtime API and proof consumers.
Run through scripts/memcap.sh with the same pinned tools and shared cache.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    options = parser.parse_args()
    root, source, out = options.root.resolve(), options.artifacts.resolve(), options.output.resolve()
    if out == source or out == root or root in out.parents:
        parser.error("--output must be outside the source tree and distinct from the native matrix")
    native = json.loads((source / "native-receipt.json").read_text())
    assert native["state"] == "passed" and native["failures"] == native["disagreements"] == 0
    objects = sorted(source.glob("*.o"))
    assert len(objects) == native["actual_lean_encoded_objects"] > 0
    expected = Counter((r["object_sha256"], r["table_sha256"], r["original_source_sha256"])
                       for r in native["records"])
    actual = Counter((sha(p), sha(p.with_suffix(".json")), sha(p.with_suffix(".clif"))) for p in objects)
    assert actual == expected, "native API artifacts changed since execution"
    out.mkdir(parents=True, exist_ok=False)
    binary = root / ".lake/build/bin/lean-backend"
    binary_hash, script_hash = sha(binary), sha(__file__)
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    records = []

    def report(state, **details):
        (out / "receipt.json").write_text(json.dumps({
            "state": state, "head": head, "binary_sha256": binary_hash,
            "script_sha256": script_hash, "native_receipt_sha256": sha(source / "native-receipt.json"),
            "records": records, **details,
            "limits": "Ordinary lowering with explicit allocators and original unit eligibility; mixed-TryCall and optimized production adapters remain separate obligations.",
        }, indent=2) + "\n")

    env = dict(os.environ, OMP_NUM_THREADS="2", OMP_THREAD_LIMIT="2", LEAN_NUM_THREADS="2")
    try:
        for original in objects:
            stem = original.stem
            allocator = stem.split("-", 1)[0]
            assert allocator in ("lean", "regalloc2"), stem
            assert stem.endswith(("-plain", "-cleanup")), stem
            clif, table = original.with_suffix(".clif"), out / (stem + ".json")
            obj, log = out / (stem + ".o"), out / (stem + ".log")
            argv = [str(binary), str(clif), str(obj), "--traps", str(table), "--regalloc", allocator]
            if stem.endswith("-plain"):
                argv.append("--no-dead-cleanup")
            report("running", phase=stem)
            with log.open("w") as stream:
                result = subprocess.run(argv, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
            assert result.returncode == 0, (stem, result.returncode, log)
            text = log.read_text()
            assert "unsupported:" not in text and "compiled, unverified" not in text, (stem, log)
            wanted = json.loads(original.with_suffix(".json").read_text())
            observed = json.loads(table.read_text())
            assert wanted["functions"] and observed == wanted, (stem, "function/trap table differs")
            assert obj.read_bytes() == original.read_bytes(), (stem, "ordinary CLI differs from raw-Stock API object")
            assert sha(binary) == binary_hash and sha(__file__) == script_hash
            assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == head
            records.append({
                "stem": stem, "argv": argv, "functions": len(wanted["functions"]),
                "ordinary_cli_raw_stock_api_bytes_exact": True, "source_sha256": sha(clif),
                "object_sha256": sha(obj), "table_sha256": sha(table), "log_sha256": sha(log),
            })
            print("ORDINARY_BACKEND_RAW_STOCK_BYTES_EXACT " + stem, flush=True)
        assert Counter((sha(p), sha(p.with_suffix(".json")), sha(p.with_suffix(".clif")))
                       for p in objects) == expected
        report("passed", actual_cli_objects=len(records), raw_stock_api_bytes_exact=True)
    except BaseException as error:
        report("failed", error=repr(error))
        raise


if __name__ == "__main__":
    main()
