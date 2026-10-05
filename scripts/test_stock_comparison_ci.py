import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("stock_ci", Path(__file__).with_name("stock-comparison-ci.py"))
CI = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CI)


def fixture():
    return {
        "progress": "finished", "official_test_files": 2,
        "inventory": [{"test": "a.clif"}, {"test": "b.clif"}],
        "tests": [
            {"test": "a.clif", "status": "binary_test", "variants": [{"index": 0, "stage": "compile", "functions_compared": [
                {"name": "%f", "status": "identical_code_artifact"}, {"name": "%g", "status": "lean_unsupported"}]}]},
            {"test": "b.clif", "status": "non_binary_test", "variants": []}],
        "totals": {"official_test_files": 2, "inventoried_test_files": 2,
            "file_statuses": {"binary_test": 1, "non_binary_test": 1},
            "function_statuses": {"identical_code_artifact": 1, "lean_unsupported": 1},
            "test_function_compilations": 2, "exact_code_artifacts": 1,
            "failed_stock_compile_assertions": 0, "source_files_modified": 0},
        "execution_performed": False, "actual_ci_execution": False, "binary_normalization": False,
        "configuration_overrides": [], "target": "aarch64-unknown-linux-gnu",
        "full_artifact_equivalence_verified": False,
    }


def invoke(case, temp, status, report, baseline=None):
    """Run main() with a mocked pipeline that exits with `status` after writing `report`."""
    out = Path(temp) / "result"
    def pipeline(argv, **kwargs):
        case.assertEqual(argv[-1], "2")
        if report is not None:
            out.mkdir(); (out / "results.json").write_text(json.dumps(report))
        return SimpleNamespace(returncode=status)
    argv = ["ci", "--out", str(out)]
    if baseline is not None:
        path = Path(temp) / "baseline.json"; path.write_text(json.dumps(baseline))
        argv += ["--baseline", str(path)]
    env = {"CI_HEAD_SHA": "a" * 40, "GITHUB_RUN_ID": "123", "GITHUB_RUN_ATTEMPT": "2"}
    with patch.object(sys, "argv", argv), patch.dict(os.environ, env), \
         patch.object(CI.subprocess, "run", side_effect=pipeline):
        return CI.main()


class CIReportTests(unittest.TestCase):
    def test_complete_measurement_can_have_gaps(self):
        self.assertEqual(CI.validate_report(fixture())["exact_code_artifacts"], 1)

    def test_partial_run_is_rejected(self):
        for change in (lambda r: r.update(progress="running"), lambda r: r["tests"].pop(),
                       lambda r: r["inventory"].pop()):
            report = fixture(); change(report)
            with self.assertRaises(ValueError): CI.validate_report(report)

    def test_duplicate_or_wrong_test_is_rejected(self):
        for replacement in ("a.clif", "missing.clif"):
            report = fixture(); report["tests"][1]["test"] = replacement
            with self.assertRaises(ValueError): CI.validate_report(report)

    def test_crashes_and_missing_reference_outputs_are_rejected(self):
        for status in ("harness_error", "reference_export_failed", "stock_parser_error"):
            report = fixture(); report["tests"][0]["status"] = status
            with self.assertRaises(ValueError): CI.validate_report(report)
        for status in ("reference_missing", "shared_input_missing", "lean_compilation_failed"):
            report = fixture(); report["tests"][0]["variants"][0]["functions_compared"][0]["status"] = status
            with self.assertRaises(ValueError): CI.validate_report(report)

    def test_invalid_totals_and_assertions_are_rejected(self):
        for field in ("exact_code_artifacts", "test_function_compilations", "failed_stock_compile_assertions", "source_files_modified"):
            report = fixture(); report["totals"][field] += 1
            with self.assertRaises(ValueError): CI.validate_report(report)

    def test_finished_measurement_becomes_success_only_with_valid_report(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(invoke(self, temp, 10, fixture()), 0)
            summary = json.loads((Path(temp) / "result.ci-summary.json").read_text())
            self.assertEqual(summary["schema"], 2)
            self.assertEqual(summary["run_attempt"], 2)
            self.assertEqual(summary["pipeline_exit_code"], 10)
            self.assertTrue(summary["measurement_complete"])
            self.assertGreater(summary["peak_runner_memory_used_bytes"], 0)
            self.assertEqual(summary["matched"], [["a.clif", 0, "compile", 0, "%f"]])
            self.assertIn("scripts/stock-compiler-compare.py", summary["harness_sha256"])
            self.assertEqual(summary["baseline_comparison"], {"available": False, "reason": "no baseline lookup"})

    def test_pipeline_failure_or_missing_report_cannot_publish(self):
        # 1 is a Python crash, 0 is never a finished measurement.
        for status, report, error in ((9, None, SystemExit), (1, fixture(), SystemExit), (0, fixture(), SystemExit),
                                      (10, None, FileNotFoundError),
                                      (10, dict(fixture(), progress="running"), ValueError)):
            with tempfile.TemporaryDirectory() as temp:
                with self.assertRaises(error): invoke(self, temp, status, report)
                self.assertFalse((Path(temp) / "result.ci-summary.json").exists())


def baseline(matched, harness, schema=2, **found):
    summary = {"schema": schema, "run_id": 77, "run_attempt": 1, "head_sha": "b" * 40,
               "matched": matched, "harness_sha256": harness}
    return {"available": True, "run_id": 77, "run_attempt": 1, "head_sha": "b" * 40, "summary": summary, **found}


class BaselineTests(unittest.TestCase):
    A, B, C = ["a.clif", 0, "compile", 0, "%f"], ["a.clif", 0, "compile", 1, "%f"], ["b.clif", 1, "run", 0, "%g"]

    def test_gained_lost_and_changed_harness(self):
        result = CI.compare_with_baseline([self.A, self.C], {"x": "1", "y": "2"},
                                          baseline([self.A, self.B], {"x": "1", "y": "3", "z": "4"}))
        self.assertTrue(result["available"])
        self.assertEqual((result["gained"], result["lost"]), ([self.C], [self.B]))
        self.assertEqual((result["gained_count"], result["lost_count"], result["baseline_exact_code_artifacts"]), (1, 1, 2))
        self.assertEqual(result["harness_changed"], ["y", "z"])
        self.assertEqual((result["run_id"], result["head_sha"]), (77, "b" * 40))

    def test_same_name_at_another_position_is_another_output(self):
        result = CI.compare_with_baseline([self.B], {}, baseline([self.A], {}))
        self.assertEqual((result["gained_count"], result["lost_count"]), (1, 1))

    def test_lists_are_bounded_but_counts_are_complete(self):
        many = [["a.clif", 0, "compile", i, "%f"] for i in range(CI.LISTED + 5)]
        result = CI.compare_with_baseline([], {}, baseline(many, {}))
        self.assertEqual((len(result["lost"]), result["lost_count"]), (CI.LISTED, CI.LISTED + 5))

    def test_missing_old_or_foreign_baseline_is_unavailable(self):
        for found, reason in (({"available": False, "reason": "none found"}, "none found"),
                              (baseline([], {}, schema=1), "schema 1"),
                              (baseline([], {}, run_id=78), "does not belong")):
            result = CI.compare_with_baseline([self.A], {}, found)
            self.assertFalse(result["available"]); self.assertIn(reason, result["reason"])

    def test_summary_records_the_comparison(self):
        with tempfile.TemporaryDirectory() as temp:
            harness = CI.harness_hashes()
            self.assertEqual(invoke(self, temp, 10, fixture(), baseline([self.B], harness)), 0)
            result = json.loads((Path(temp) / "result.ci-summary.json").read_text())["baseline_comparison"]
            self.assertEqual((result["gained"], result["lost"], result["harness_changed"]), ([self.A], [self.B], []))


if __name__ == "__main__":
    unittest.main()
