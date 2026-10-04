#!/usr/bin/env python3
"""Run the full pipeline; CI success means a complete, valid measurement."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
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
    if report["execution_performed"] or report["actual_ci_execution"] or report["binary_normalization"] or report["configuration_overrides"]:
        raise ValueError("comparison contract changed")
    return totals


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
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    head = os.environ.get("CI_HEAD_SHA", "")
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        parser.error("CI_HEAD_SHA must identify the tested PR commit")
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
    if result.returncode not in (0, 1):
        raise SystemExit(result.returncode)
    report = json.loads((out / "results.json").read_text())
    totals = validate_report(report)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    data = {"schema": 1, "measurement_complete": True, "head_sha": head,
            "run_id": int(os.environ["GITHUB_RUN_ID"]),
            "run_attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
            "target": report["target"], "totals": totals,
            "full_artifact_equivalence_verified": report["full_artifact_equivalence_verified"],
            "elapsed_seconds": round(elapsed, 3),
            "cpu_seconds": round(after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime, 3),
            "peak_runner_memory_used_bytes": max(samples),
            "pipeline_exit_code": result.returncode}
    summary.write_text(json.dumps(data, indent=2) + "\n")
    print("Complete CI measurement:", summary, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
