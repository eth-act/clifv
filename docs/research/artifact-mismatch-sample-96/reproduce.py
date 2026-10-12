#!/usr/bin/env python3
"""Reproduce the diagnostic sample from an extracted CI comparison artifact.

Run with Python 3.14 and capstone==5.0.9. Outputs are diagnostic evidence;
disassembly never changes the compiler comparison verdict.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

from capstone import Cs, CS_ARCH_ARM64, CS_MODE_LITTLE_ENDIAN, __version__

SEED = 13455975217634421948


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("comparison", type=Path, help="Directory containing results.json and files/")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = (args.comparison / "results.json").read_bytes()
    report = json.loads(raw)
    assert report["progress"] == "finished"
    assert len(report["tests"]) == report["official_test_files"] == 1302
    indexed = {}
    for case in report["tests"]:
        for variant in case["variants"]:
            for row_index, row in enumerate(variant["functions_compared"]):
                if row["status"] == "different_code_artifact":
                    key = (case["test"], variant["index"], row["name"], row_index)
                    assert key not in indexed
                    indexed[key] = (case, variant, row)
    population = sorted(indexed)
    assert len(population) == report["totals"]["function_statuses"]["different_code_artifact"]
    selected = random.Random(SEED).sample(population, 96)
    decoder = Cs(CS_ARCH_ARM64, CS_MODE_LITTLE_ENDIAN)
    decoder.skipdata = True
    entries = []
    for number, key in enumerate(selected, 1):
        case, variant, row = indexed[key]
        directory = args.comparison / "files" / key[0].removesuffix(".clif")
        stock_dir = directory / "stock" / f"variant-{key[1]}"
        stock = []
        for path in sorted(stock_dir.glob("*.json")):
            meta = json.loads(path.read_text())
            if isinstance(meta, dict) and meta.get("name") == key[2] and "relocations" in meta and (row.get("index") is None or meta.get("index", meta.get("id")) == row["index"]):
                stock.append((path, meta))
        assert len(stock) == 1, (key, row.get("index"), len(stock))
        stock_path, stock_meta = stock[0]
        contracts = [(i, c) for i, c in enumerate(variant["lean_compilations"]) if key[2] in c["functions"] and (row.get("index") is None or row["index"] in c.get("function_indices", []))]
        assert len(contracts) == 1
        compilation, contract = contracts[0]
        group = directory / f"variant-{key[1]}" / f"compilation-{compilation}"
        lean_dir = group / "lean" / "dump"
        name = key[2].removeprefix("%")
        stock_bytes = stock_path.with_suffix(".bin").read_bytes()
        lean_bytes = (lean_dir / (name + ".bin")).read_bytes()
        assert sha(stock_bytes) == row["bytes"]["left_sha256"]
        assert sha(lean_bytes) == row["bytes"]["right_sha256"]
        assert contract["contract_verified"] and contract["receipt"]["request"] == contract["request"]
        assert sha((group / "input.clif").read_bytes()) == contract["request"]["input_sha256"]
        disassemble = lambda code: [f"{i.address:04x}: {i.bytes.hex()}  {i.mnemonic} {i.op_str}".rstrip() for i in decoder.disasm(code, 0)]
        evidence = {
            "number": number, "test": key[0], "variant": key[1], "function": key[2],
            "row_index": key[3], "stage": variant["stage"], "isa_index": variant["isa_index"],
            "command_index": variant["command_index"], "compilation": compilation,
            "comparison": row, "request": contract["request"], "receipt": contract["receipt"],
            "original_source_sha256": case["source_sha256"],
            "stock_source": stock_path.with_suffix(".clif").read_text(),
            "adapted_source": stock_path.with_suffix(".lean.clif").read_text(),
            "stock_metadata": stock_meta,
            "lean_metadata": json.loads((lean_dir / (name + ".metadata.json")).read_text()),
            "stock_code_hex": stock_bytes.hex(), "lean_code_hex": lean_bytes.hex(),
            "stock_disassembly": disassemble(stock_bytes), "lean_disassembly": disassemble(lean_bytes),
            "artifact_paths": {"stock": str(stock_path.relative_to(args.comparison)),
                               "lean": str((lean_dir / (name + ".bin")).relative_to(args.comparison))},
        }
        filename = f"cases/{number:02d}.json"
        write(args.output / filename, evidence)
        entries.append({"number": number, "test": key[0], "variant": key[1], "function": key[2], "row_index": key[3], "evidence": filename})
    write(args.output / "manifest.json", {
        "schema": 1, "run_url": "https://github.com/eth-act/clifv/actions/runs/38093345756",
        "artifact_id": 11684324784, "artifact_name": "stock-comparison-artifacts-1",
        "checkout_commit": "bc3a34cf018ea024ef8df4b3bda3fde28ebd5874",
        "upstream_commit": report["upstream_commit"], "results_sha256": sha(raw),
        "lean_source_tree_sha256": report["lean_source_tree_sha256"],
        "source_hashes": report["source_hashes"], "binary_hashes": report["binary_hashes"],
        "totals": report["totals"], "population_filter": "status == different_code_artifact",
        "sampling_unit": "test path, variant index, function name, comparison row index occurrence",
        "sampling_method": "Python random.Random(seed).sample(sorted(population), 96); no replacement or redraw",
        "seed": SEED, "seed_origin": "One secrets.randbits(64) draw before viewing selected diagnoses",
        "decoder": f"capstone {__version__}; ARM64 little endian; base address 0; skipdata enabled",
        "population": population, "selected": entries,
    })
    print(f"Verified and captured {len(entries)} samples from {len(population)} mismatches.")


if __name__ == "__main__":
    main()
