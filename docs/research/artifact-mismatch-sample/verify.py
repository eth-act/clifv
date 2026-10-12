#!/usr/bin/env python3
"""Recheck sample identities, receipts, raw artifacts and checkout provenance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("comparison", type=Path)
    parser.add_argument("evidence", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(root / "scripts"))
    spec = importlib.util.spec_from_file_location("stock", root / "scripts/stock-compiler-compare.py")
    stock = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(stock)
    manifest = json.loads((args.evidence / "manifest.json").read_text())
    raw = (args.comparison / "results.json").read_bytes()
    assert sha(raw) == manifest["results_sha256"]
    report = json.loads(raw)
    indexed = {(c["test"], v["index"], f["name"], i): (c, v, f)
               for c in report["tests"] for v in c["variants"]
               for i, f in enumerate(v["functions_compared"])
               if f["status"] == "different_code_artifact"}
    population = sorted(indexed)
    assert population == [tuple(x) for x in manifest["population"]]
    selected = random.Random(manifest["seed"]).sample(population, 32)
    assert len(manifest["selected"]) == len(set(selected)) == 32
    assert [e["number"] for e in manifest["selected"]] == list(range(1, 33))
    for name, expected in manifest["source_hashes"].items():
        assert sha((root / name).read_bytes()) == expected, name
    tree = hashlib.sha256()
    for path in sorted([*root.joinpath("FV").rglob("*.lean"), *root.joinpath("FVTest").rglob("*.lean")]):
        tree.update(str(path.relative_to(root)).encode() + b"\0" + path.read_bytes() + b"\0")
    assert tree.hexdigest() == manifest["lean_source_tree_sha256"]
    for key, entry in zip(selected, manifest["selected"]):
        case, variant, row = indexed[key]
        assert key == (entry["test"], entry["variant"], entry["function"], entry["row_index"])
        evidence = json.loads((args.evidence / entry["evidence"]).read_text())
        assert evidence["comparison"] == row
        assert evidence["number"] == entry["number"]
        stock_path = args.comparison / evidence["artifact_paths"]["stock"]
        lean_dir = (args.comparison / evidence["artifact_paths"]["lean"]).parent.parent
        group = lean_dir.parent
        request = json.loads((group / "stock-config.json").read_text())
        receipt = json.loads((group / "configuration-receipt.json").read_text())
        source = (group / "input.clif").read_bytes()
        assert stock.verify_receipt(request, receipt, source) is None
        assert request == evidence["request"] and receipt == evidence["receipt"]
        repeat_dir = stock_path.parent.parent.parent / "stock-repeat" / stock_path.parent.name
        assert stock.repeat_check(stock_path.parent, repeat_dir)
        result = stock.compare_function(key[2], (stock_path, json.loads(stock_path.read_text())), lean_dir, True, True)
        assert result == row, key
        assert evidence["stock_code_hex"] == stock_path.with_suffix(".bin").read_bytes().hex()
        assert evidence["lean_code_hex"] == (lean_dir / "dump" / (key[2].removeprefix("%") + ".bin")).read_bytes().hex()
        assert evidence["stock_source"] == stock_path.with_suffix(".clif").read_text()
        assert evidence["adapted_source"] == stock_path.with_suffix(".lean.clif").read_text()
        assert sha((stock_path.parent.parent.parent / "original.clif").read_bytes()) == case["source_sha256"]
    verification = {
        "source_hashes_match_checkout": True, "lean_source_tree_matches_checkout": True,
        "all_32_sample_identities_reproduced": True, "all_32_settings_receipts_verified": True,
        "all_32_stock_repeats_verified": True, "all_32_comparison_rows_recomputed_equal": True,
        "all_32_dump_object_byte_relocation_alignment_checks_pass": True,
        "all_32_preserved_input_and_code_snapshots_match": True,
        "verified_case_numbers": list(range(1, 33)),
    }
    (args.evidence / "verification.json").write_text(json.dumps(verification, indent=2) + "\n")
    print("Verified every sampled identity, receipt, repeat, artifact and source snapshot.")


if __name__ == "__main__":
    main()
