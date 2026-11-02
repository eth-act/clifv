#!/usr/bin/env python3
"""Break a stock comparison down by why outputs differ or are rejected.

Usage: python3 scripts/stock-comparison-breakdown.py <comparison-output-dir>
(the directory holding results.json and files/, e.g. a CI artifact's target/ci-comparison).

Exact outputs: by stage and size. Different outputs: whether each side sets up a frame, whether
Lean's code is longer, and the most common first differing instruction words. Rejections: by
setting, and by Lean's first error for the function. docs/STOCK-AGREEMENT-GAPS.md explains the
categories.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re

FRAME = 0xa9bf7bfd  # stp x29, x30, [sp, #-16]!
COMPILED = {"identical_code_artifact", "different_code_artifact", "unsupported_configuration",
            "lean_unsupported", "lean_compilation_failed"}
ERROR = re.compile(r"^lean-backend: .*?: %?(\S+?): unsupported: (.*)$")


def words(path):
    data = path.read_bytes()
    return [int.from_bytes(data[i:i + 4], "little") for i in range(0, len(data) - 3, 4)]


def stock_artifacts(directory):
    """Stock code artifacts by recorded position ("index") and by name."""
    by_index, by_name = {}, {}
    for path in directory.glob("*.json"):
        meta = json.loads(path.read_text())
        if isinstance(meta, dict) and "relocations" in meta and "name" in meta:
            if isinstance(meta.get("index"), int):
                by_index[meta["index"]] = path.with_suffix(".bin")
            by_name[meta["name"]] = path.with_suffix(".bin")
    return by_index, by_name


def outputs(base, report):
    """(test, variant, row, stock code, Lean compilation directory) for every function output."""
    for test in report["tests"]:
        files = base / "files" / test["test"].removesuffix(".clif")
        for variant in test["variants"]:
            by_index, by_name = stock_artifacts(files / "stock" / f"variant-{variant['index']}")
            compilations = variant["lean_compilations"]
            pending = 0  # compile stage: one compilation per compiled function, in order
            for position, row in enumerate(variant["functions_compared"]):
                index = row.get("index", position)
                stock = by_index.get(index) or by_name.get(row["name"])
                compiled = None
                if variant["stage"] == "run" and compilations:
                    compiled = 0
                elif row["status"] in COMPILED and pending < len(compilations) and \
                        compilations[pending]["functions"] == [row["name"]]:
                    compiled, pending = pending, pending + 1
                lean = None if compiled is None else \
                    files / f"variant-{variant['index']}" / f"compilation-{compiled}" / "lean"
                yield test, variant, row, stock, lean


def normalize(text):
    return re.sub(r"\d+", "N", re.sub(r"\bv\d+", "vN", text))[:110]


def first_error(lean, name):
    """Lean's first `unsupported` line for this function (Lean prints `?` for names like u0:1)."""
    fallback = None
    stderr = lean.parent / "lean.stderr"
    for line in (stderr.read_text(errors="replace").splitlines() if stderr.exists() else []):
        m = ERROR.match(line)
        if m and m[1] == name.removeprefix("%"):
            return normalize(m[2])
        if m and m[1] == "?" and fallback is None:
            fallback = normalize(m[2])
    return fallback or "no matching error line"


def table(counter, limit=None):
    return "\n".join(f"  {n:6,}  {key}" for key, n in counter.most_common(limit))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("comparison", type=Path)
    parser.add_argument("--top", type=int, default=12, help="rows per ranking")
    args = parser.parse_args()
    report = json.loads((args.comparison / "results.json").read_text())
    statuses, stages, sizes, shapes, pairs, settings, operations = (Counter() for _ in range(7))
    for test, variant, row, stock, lean in outputs(args.comparison, report):
        status = row["status"]
        statuses[status] += 1
        if status == "identical_code_artifact":
            stages[f"{variant['stage']}, {test['category']}"] += 1
            sizes[len(words(stock))] += 1
        elif status == "different_code_artifact":
            name = row["name"].removeprefix("%")
            s, l = words(stock), words(lean / "dump" / f"{name}.bin")
            frame = ("stock frame" if s[:1] == [FRAME] else "stock frameless") + ", " + \
                    ("Lean frame" if l[:1] == [FRAME] else "Lean frameless")
            length = "Lean longer" if len(l) > len(s) else "Lean shorter" if len(l) < len(s) else "same length"
            shapes[f"{frame}, {length}"] += 1
            first = next((i for i, (a, b) in enumerate(zip(s, l)) if a != b), min(len(s), len(l)))
            pairs[f"word {first}: stock {s[first] if first < len(s) else 0:08x}, "
                  f"Lean {l[first] if first < len(l) else 0:08x}"] += 1
        elif status == "unsupported_configuration":
            settings[normalize(re.sub(r"; implemented policy is .*", "", row.get("reason", "")))] += 1
        elif status == "lean_unsupported":
            operations[first_error(lean, row["name"]) if lean else "not compiled"] += 1
    total = sum(statuses.values()) - statuses["expected_stock_rejection_no_binary"]
    print(f"Stock outputs: {total:,} (plus {statuses['expected_stock_rejection_no_binary']:,} expected stock rejections)")
    print(table(statuses))
    quartiles = sorted(sizes.elements())
    if quartiles:
        q = [quartiles[len(quartiles) * k // 4] for k in (1, 2, 3)]
        print(f"\nExact outputs by stage and test directory (instructions: quartiles {q}, max {quartiles[-1]}):")
        print(table(stages, args.top))
    print("\nDifferent outputs by frame and length:")
    print(table(shapes))
    print("\nFirst differing instruction words (stock vs Lean):")
    print(table(pairs, args.top))
    print("\nRejected for a setting:")
    print(table(settings, args.top))
    print("\nRejected for an operation, by Lean's first error for the function:")
    print(table(operations, args.top))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
