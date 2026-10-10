import copy
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location("stock_delta", Path(__file__).with_name("stock-comparison-delta.py"))
DELTA = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DELTA)


def report(exact):
    functions = [{"index": i, "name": f"%f{i}", "exact_code_artifact": match,
                  "status": "identical_code_artifact" if match else "different_code_artifact"}
                 for i, match in enumerate(exact)]
    return {"progress": "finished", "upstream_commit": "pin", "target": "aarch64",
            "inventory": [{"test": "test.clif", "sha256": "source"}],
            "totals": {"failed_stock_compile_assertions": 0,
                       "nonrepeatable_reference_stages": 0, "source_files_modified": 0},
            "tests": [{"test": "test.clif", "status": "binary_test", "variants": [
                {"index": 0, "stage": "compile", "target": "aarch64", "flags": [],
                 "isa_flags": [], "functions_compared": functions}]}]}


class DeltaTests(unittest.TestCase):
    def test_gain_preserves_each_existing_match(self):
        result = DELTA.compare(report([True, False]), report([True, True]),
                               [("test.clif", "%f1")], full_suite=True)
        self.assertTrue(result["checkpoint_passed"])
        self.assertEqual(result["gained"], [("test.clif", 0, 1, "%f1")])

    def test_aggregate_gain_cannot_hide_a_lost_match(self):
        result = DELTA.compare(report([True, False, False]), report([False, True, True]))
        self.assertGreater(result["candidate_exact"], result["baseline_exact"])
        self.assertFalse(result["checkpoint_passed"])
        self.assertEqual(len(result["lost"]), 1)

    def test_gain_cannot_hide_new_rejection(self):
        candidate = report([True, False])
        candidate["tests"][0]["variants"][0]["functions_compared"][1]["status"] = "lean_unsupported"
        result = DELTA.compare(report([False, False]), candidate)
        self.assertFalse(result["checkpoint_passed"])
        self.assertEqual(len(result["new_rejections"]), 1)

    def test_missing_or_nonexact_focused_case_fails(self):
        for name in ("%missing", "%f0"):
            self.assertFalse(DELTA.compare(report([False, False]), report([False, True]),
                                           [("test.clif", name)])["checkpoint_passed"])

    def test_changed_settings_or_inventory_are_invalid(self):
        for field in ("flags", "stage", "target"):
            candidate = report([True])
            candidate["tests"][0]["variants"][0][field] = "changed"
            with self.assertRaisesRegex(ValueError, "different settings"):
                DELTA.compare(report([False]), candidate)
        candidate = report([True])
        candidate["inventory"][0]["sha256"] = "changed"
        with self.assertRaisesRegex(ValueError, "different inventory"):
            DELTA.compare(report([False]), candidate)

    def test_missing_duplicate_and_incomplete_measurements_are_invalid(self):
        baseline = report([False])
        candidates = [report([]), report([True]), report([True]), report([True])]
        candidates[1]["progress"] = "running"
        functions = candidates[2]["tests"][0]["variants"][0]["functions_compared"]
        functions.append(copy.deepcopy(functions[0]))
        candidates[3]["tests"][0]["status"] = "harness_error"
        for candidate in candidates:
            with self.assertRaises(ValueError):
                DELTA.compare(baseline, candidate)

    def test_full_suite_rejects_partial_inventory(self):
        baseline, candidate = report([False]), report([True])
        for value in (baseline, candidate):
            value["inventory"].append({"test": "omitted.clif", "sha256": "source"})
        with self.assertRaisesRegex(ValueError, "full inventory"):
            DELTA.compare(baseline, candidate, full_suite=True)

    def test_bad_reference_measurement_is_invalid(self):
        for field in ("failed_stock_compile_assertions", "source_files_modified"):
            candidate = report([True])
            candidate["totals"][field] = 1
            with self.assertRaises(ValueError):
                DELTA.compare(report([False]), candidate)

    def test_unstable_reference_cannot_support_compiled_comparison(self):
        baseline, candidate = report([False]), report([True])
        for value in (baseline, candidate):
            value["tests"][0]["variants"][0]["reference_repeat_verified"] = False
        with self.assertRaisesRegex(ValueError, "nonrepeatable reference"):
            DELTA.compare(baseline, candidate)


if __name__ == "__main__":
    unittest.main()
