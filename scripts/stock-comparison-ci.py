#!/usr/bin/env python3
"""Run the full pipeline; CI success means a complete, valid measurement.

The summary lists every exact output and hashes the measuring code. Given a baseline summary
from `main` (`stock-comparison-baseline.py`), it also lists the outputs gained and lost since
then; `stock-comparison-ratchet.py` fails on lost ones.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 2
FINISHED_WITH_GAPS = 10  # stock-compiler-compare.py's exit code for a finished measurement
# The measuring code: a change here can move the numbers without any compiler change.
HARNESS = ["scripts/stock-compiler-compare.py", "scripts/stock-comparison-ci.py",
           "scripts/stock-compiler-comparison.sh", "scripts/stock_common.py", "scripts/byte_compare.py",
           "scripts/prejit-export-build.sh", "scripts/patches/prejit-export.patch",
           "tools/prejit-export/Cargo.toml", "tools/prejit-export/Cargo.lock", "tools/prejit-export/src/**/*",
           "FVTest/Backend/StockConfig.lean", "FVTest/Backend/Main.lean",
           ".github/workflows/stock-compiler-comparison.yml"]
LISTED = 200  # gained/lost entries kept in the summary; the counts are always complete
FILE_STATUSES = {"binary_test", "non_binary_test", "no_lean_target", "stock_parser_warning_skip"}
FUNCTION_STATUSES = {"identical_code_artifact", "different_code_artifact", "unsupported_configuration",
                     "lean_unsupported", "expected_stock_rejection_no_binary"}


def validate_report(report):
    """Do not turn a crashed, partial, or damaged baseline into a green CI run."""
    if report.get("progress") != "finished":
        raise ValueError("comparison did not finish")
    totals, tests = report["totals"], report["tests"]
    inventory = report["inventory"]
    official = report["official_test_files"]
    if not official or len(inventory) != official or len(tests) != official:
        raise ValueError("comparison did not process the complete official inventory")
    paths = [entry["test"] for entry in inventory]
    if len(set(paths)) != official or Counter(paths) != Counter(test["test"] for test in tests):
        raise ValueError("test results do not cover the inventory exactly once")
    if totals["official_test_files"] != official or totals["inventoried_test_files"] != official:
        raise ValueError("inventory totals disagree")
    if any(test["status"] not in FILE_STATUSES for test in tests):
        raise ValueError("reference export, parser, or comparison harness failed")
    functions = [f for test in tests for variant in test["variants"] for f in variant["functions_compared"]]
    if any(f["status"] not in FUNCTION_STATUSES for f in functions):
        raise ValueError("unexpected compiler or input failure")
    if totals["function_statuses"] != dict(Counter(f["status"] for f in functions)):
        raise ValueError("function totals disagree")
    if totals["test_function_compilations"] != len(functions):
        raise ValueError("function count disagrees")
    if totals["file_statuses"] != dict(Counter(test["status"] for test in tests)):
        raise ValueError("file totals disagree")
    if totals["exact_code_artifacts"] != totals["function_statuses"].get("identical_code_artifact", 0):
        raise ValueError("match total disagrees")
    if totals["failed_stock_compile_assertions"] or totals["source_files_modified"]:
        raise ValueError("stock assertions failed or stock test sources changed")
    return totals


def matched_entries(report):
    """Every exact output as [test, variant index, stage, position in the variant, function]."""
    return sorted([test["test"], variant["index"], variant["stage"], position, row["name"]]
                  for test in report["tests"] for variant in test["variants"]
                  for position, row in enumerate(variant["functions_compared"])
                  if row["status"] == "identical_code_artifact")


def harness_hashes(root=ROOT):
    files = sorted({path for pattern in HARNESS for path in root.glob(pattern) if path.is_file()})
    return {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest() for path in files}


def baseline_summary(found):
    """(summary, None, False) for the baseline from `stock-comparison-baseline.py`, or
    (None, why there is none, whether that is a failure). There is no baseline when none exists
    or main's summary has another schema (made before or after this one's format). Anything
    else that is not a valid baseline is a failure, which fails the lost-match check."""
    if not isinstance(found, dict) or not isinstance(found.get("available"), bool):
        return None, "the baseline lookup result is malformed", True
    if not found["available"]:
        return None, str(found.get("reason") or "no baseline")[:200], found.get("failed") is not False
    summary = found.get("summary")
    schema = summary.get("schema") if isinstance(summary, dict) else None
    if not isinstance(schema, int):
        return None, "the baseline summary is malformed", True
    if schema != SCHEMA:
        return None, f"the main run has summary schema {schema}, not {SCHEMA}", False
    if (summary.get("run_id"), summary.get("run_attempt"), summary.get("head_sha")) != (
            found.get("run_id"), found.get("run_attempt"), found.get("head_sha")):
        return None, "the baseline summary does not belong to its run", True
    if not well_formed(summary):
        return None, "the baseline summary is malformed", True
    return summary, None, False


def well_formed(summary):
    """The baseline fields this comparison reads: matched entries and harness hashes."""
    entries, hashes = summary.get("matched"), summary.get("harness_sha256")
    return (isinstance(entries, list)
            and all(isinstance(e, list) and len(e) == 5 and all(isinstance(x, (str, int)) for x in e)
                    for e in entries)
            and isinstance(hashes, dict) and all(isinstance(v, str) for v in hashes.values()))


def compare_with_baseline(matched, harness, found):
    """Exact outputs gained and lost since the baseline, and the measuring files that changed."""
    base, reason, failed = baseline_summary(found)
    if base is None:
        return {"available": False, "failed": failed, "reason": reason}
    now, before = {tuple(e) for e in matched}, {tuple(e) for e in base["matched"]}
    gained, lost = sorted(now - before), sorted(before - now)
    old = base["harness_sha256"]
    return {"available": True, "run_id": base["run_id"], "run_attempt": base["run_attempt"],
            "head_sha": base["head_sha"], "baseline_exact_code_artifacts": len(before),
            "gained_count": len(gained), "lost_count": len(lost),
            "gained": [list(e) for e in gained[:LISTED]], "lost": [list(e) for e in lost[:LISTED]],
            "harness_changed": sorted(p for p in old.keys() | harness.keys() if old.get(p) != harness.get(p))}


def runner_memory_used():
    """Whole-runner RAM use, including the OS; not a single-process RSS."""
    values = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key, value = line.split(":", 1)
        if key in ("MemTotal", "MemAvailable"):
            values[key] = int(value.split()[0]) * 1024
    return values["MemTotal"] - values["MemAvailable"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--baseline", type=Path, help="output of stock-comparison-baseline.py")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    head = os.environ.get("CI_HEAD_SHA", "")
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        parser.error("CI_HEAD_SHA must identify the tested commit")
    out = args.out.resolve()
    summary = out.with_name(out.name + ".ci-summary.json")
    if summary.exists():
        parser.error("choose a fresh output directory")
    stop = threading.Event()
    samples = []

    def sample():
        while True:
            samples.append(runner_memory_used())
            if stop.wait(0.1):
                return

    sampler = threading.Thread(target=sample)
    sampler.start()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    try:
        result = subprocess.run(["bash", str(ROOT / "scripts/stock-compiler-comparison.sh"),
                                 "--out", str(out), "--jobs", str(args.jobs)], cwd=ROOT)
    finally:
        elapsed = time.monotonic() - start
        stop.set()
        sampler.join()
    if result.returncode != FINISHED_WITH_GAPS:
        raise SystemExit(result.returncode or 1)
    report = json.loads((out / "results.json").read_text())
    totals = validate_report(report)
    matched, harness = matched_entries(report), harness_hashes()
    if args.baseline is None:
        found = {"available": False, "failed": False, "reason": "no baseline lookup"}
    elif not args.baseline.exists():
        found = {"available": False, "failed": True, "reason": "the baseline lookup wrote no result"}
    else:
        try:
            found = json.loads(args.baseline.read_text())
        except ValueError:
            found = None  # reported as malformed
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    data = {"schema": SCHEMA, "measurement_complete": True, "head_sha": head,
            "run_id": int(os.environ["GITHUB_RUN_ID"]),
            "run_attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
            "target": report["target"], "totals": totals,
            "full_artifact_equivalence_verified": report["full_artifact_equivalence_verified"],
            "elapsed_seconds": round(elapsed, 3),
            "cpu_seconds": round(after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime, 3),
            "peak_runner_memory_used_bytes": max(samples),
            "pipeline_exit_code": result.returncode,
            "matched": matched, "harness_sha256": harness,
            "baseline_comparison": compare_with_baseline(matched, harness, found)}
    summary.write_text(json.dumps(data, indent=2) + "\n")
    print("Complete CI measurement:", summary, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
