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
            {"test": "a.clif", "status": "binary_test", "variants": [{"functions_compared": [
                {"status": "identical_code_artifact"}, {"status": "lean_unsupported"}]}]},
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

    def test_invalid_totals_assertions_and_contract_are_rejected(self):
        for field in ("exact_code_artifacts", "test_function_compilations", "failed_stock_compile_assertions", "source_files_modified"):
            report = fixture(); report["totals"][field] += 1
            with self.assertRaises(ValueError): CI.validate_report(report)
        for field in ("execution_performed", "actual_ci_execution", "binary_normalization", "configuration_overrides"):
            report = fixture(); report[field] = True
            with self.assertRaises(ValueError): CI.validate_report(report)

    def invoke(self, temp, status, report):
        out = Path(temp) / "result"
        def pipeline(argv, **kwargs):
            self.assertEqual(argv[-1], "2")
            if report is not None:
                out.mkdir(); (out / "results.json").write_text(json.dumps(report))
            return SimpleNamespace(returncode=status)
        env = {"CI_HEAD_SHA": "a" * 40, "GITHUB_RUN_ID": "123", "GITHUB_RUN_ATTEMPT": "2"}
        with patch.object(sys, "argv", ["ci", "--out", str(out)]), patch.dict(os.environ, env), \
             patch.object(CI.subprocess, "run", side_effect=pipeline):
            return CI.main()

    def test_expected_exit_one_becomes_success_only_with_valid_report(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(self.invoke(temp, 1, fixture()), 0)
            summary = json.loads((Path(temp) / "result.ci-summary.json").read_text())
            self.assertEqual(summary["run_attempt"], 2)
            self.assertEqual(summary["pipeline_exit_code"], 1)
            self.assertTrue(summary["measurement_complete"])
            self.assertGreater(summary["peak_runner_memory_used_bytes"], 0)

    def test_pipeline_failure_or_missing_report_cannot_publish(self):
        for status, report, error in ((9, None, SystemExit), (1, None, FileNotFoundError),
                                      (1, dict(fixture(), progress="running"), ValueError)):
            with tempfile.TemporaryDirectory() as temp:
                with self.assertRaises(error): self.invoke(temp, status, report)
                self.assertFalse((Path(temp) / "result.ci-summary.json").exists())


if __name__ == "__main__":
    unittest.main()
