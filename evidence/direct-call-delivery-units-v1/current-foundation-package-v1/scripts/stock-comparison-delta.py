#!/usr/bin/env python3
"""Compare finished stock measurements by function identity; fail on lost matches."""
import argparse
import json
from pathlib import Path


COMPILED = {"identical_code_artifact", "different_code_artifact"}


def rows(report):
    if report.get("progress") != "finished":
        raise ValueError("measurement is not finished")
    result = {}
    for test in report["tests"]:
        if test["status"] == "harness_error":
            raise ValueError(f"harness error: {test['test']}")
        for variant in test["variants"]:
            settings = {k: variant[k] for k in ("target", "flags", "isa_flags", "stage")}
            for function in variant["functions_compared"]:
                key = (test["test"], variant["index"], function["index"], function["name"])
                if key in result:
                    raise ValueError(f"duplicate function identity: {key}")
                result[key] = (settings, function)
    return result


def compare(baseline, candidate, required=(), full_suite=False):
    if "regalloc_oracle" in baseline and "regalloc_oracle" in candidate:
        if baseline["regalloc_oracle"]["sha256"] != candidate["regalloc_oracle"]["sha256"]:
            raise ValueError("different regalloc oracle")
    for field in ("upstream_commit", "target", "inventory"):
        if baseline[field] != candidate[field]:
            raise ValueError(f"different {field}")
    if full_suite:
        inventory = {row["test"] for row in baseline["inventory"]}
        for report in (baseline, candidate):
            names = [row["test"] for row in report["tests"]]
            if len(names) != len(set(names)) or set(names) != inventory:
                raise ValueError("measurement does not cover the full inventory exactly once")
    for report in (baseline, candidate):
        for field in ("failed_stock_compile_assertions", "source_files_modified"):
            if report["totals"][field]:
                raise ValueError(f"invalid measurement: {field}")
    before, after = rows(baseline), rows(candidate)
    def unstable(report):
        return sorted((test["test"], variant["index"]) for test in report["tests"]
                      for variant in test["variants"] if not variant.get("reference_repeat_verified", True))
    reference_gaps = unstable(baseline)
    if reference_gaps != unstable(candidate):
        raise ValueError("different reference repeatability")
    for report in (baseline, candidate):
        for test in report["tests"]:
            for variant in test["variants"]:
                if (test["test"], variant["index"]) in reference_gaps:
                    if any(row["status"] in COMPILED for row in variant["functions_compared"]):
                        raise ValueError("compiled function has a nonrepeatable reference")
    if before.keys() != after.keys():
        raise ValueError("different function identity sets")
    gained, lost, rejected, changed = [], [], [], []
    for key, (settings, old) in before.items():
        new_settings, new = after[key]
        if settings != new_settings:
            raise ValueError(f"different settings: {key}")
        # Reference artifacts must also be identical, whenever both were compared.
        if "bytes" in old and "bytes" in new:
            if old["bytes"]["left_sha256"] != new["bytes"]["left_sha256"]:
                raise ValueError(f"different stock bytes: {key}")
            for field in ("reference_relocations", "alignment", "traps"):
                left = old[field].get("stock") if field != "reference_relocations" else old[field]
                right = new[field].get("stock") if field != "reference_relocations" else new[field]
                if left != right:
                    raise ValueError(f"different stock {field}: {key}")
        old_exact, new_exact = bool(old.get("exact_code_artifact")), bool(new.get("exact_code_artifact"))
        if new_exact and not old_exact:
            gained.append(key)
        if old_exact and not new_exact:
            lost.append(key)
        if old["status"] in COMPILED and new["status"] not in COMPILED:
            rejected.append(key)
        if old["status"] != new["status"]:
            changed.append({"identity": key, "before": old["status"], "after": new["status"]})
    focused = []
    for test, name in required:
        matches = [(key, row) for key, (_, row) in after.items() if key[0] == test and key[3] == name]
        focused.append({"test": test, "name": name, "occurrences": len(matches),
                        "all_exact": bool(matches) and all(row.get("exact_code_artifact") for _, row in matches)})
    return {"baseline_exact": sum(bool(row.get("exact_code_artifact")) for _, row in before.values()),
            "candidate_exact": sum(bool(row.get("exact_code_artifact")) for _, row in after.values()),
            "gained": gained, "lost": lost, "new_rejections": rejected,
            "status_changes": changed, "focused": focused, "uncompared_reference_gaps": reference_gaps,
            "checkpoint_passed": bool(gained) and not lost and not rejected and all(r["all_exact"] for r in focused)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--require-full-suite", action="store_true")
    parser.add_argument("--require-exact", action="append", default=[], metavar="TEST:%FUNCTION")
    args = parser.parse_args()
    try:
        required = [item.rsplit(":", 1) for item in args.require_exact]
        if any(len(item) != 2 for item in required):
            raise ValueError("--require-exact needs TEST:%FUNCTION")
        result = compare(json.loads(args.baseline.read_text()), json.loads(args.candidate.read_text()),
                         required, args.require_full_suite)
    except (ValueError, KeyError) as error:
        parser.error(str(error))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Exact matches: {result['baseline_exact']} -> {result['candidate_exact']}; "
          f"gained {len(result['gained'])}, lost {len(result['lost'])}, "
          f"new rejections {len(result['new_rejections'])}")
    return 0 if result["checkpoint_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
