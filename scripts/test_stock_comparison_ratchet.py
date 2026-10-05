import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("stock_ratchet", Path(__file__).with_name("stock-comparison-ratchet.py"))
RATCHET = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RATCHET)

HEAD = "a" * 40
LOST = ["a.clif", 0, "compile", 3, "%f"]


def summary(lost=(), gained=(), available=True, harness_changed=()):
    comparison = {"available": False, "reason": "none found"}
    if available:
        comparison = {"available": True, "run_id": 77, "run_attempt": 1, "head_sha": "b" * 40,
                      "baseline_exact_code_artifacts": 10, "gained_count": len(gained), "lost_count": len(lost),
                      "gained": list(gained), "lost": list(lost), "harness_changed": list(harness_changed)}
    return {"run_id": 123, "head_sha": HEAD, "baseline_comparison": comparison}


class CheckTests(unittest.TestCase):
    def test_no_losses_pass(self):
        status, lines = RATCHET.check(summary(gained=[LOST]), 123, HEAD, None)
        self.assertEqual(status, 0); self.assertIn("+1 / -0", lines[0])

    def test_missing_baseline_passes_and_says_why(self):
        status, lines = RATCHET.check(summary(available=False), 123, HEAD, [])
        self.assertEqual(status, 0); self.assertIn("none found", lines[0])

    def test_losses_fail_on_pull_requests_and_main(self):
        for labels in ([], ["other"], None):
            status, lines = RATCHET.check(summary(lost=[LOST]), 123, HEAD, labels)
            self.assertEqual(status, 1)
            self.assertTrue(any("a.clif %f (compile, variant 0, function 3)" in line for line in lines))

    def test_label_accepts_losses_on_pull_requests(self):
        status, lines = RATCHET.check(summary(lost=[LOST]), 123, HEAD, [RATCHET.LABEL])
        self.assertEqual(status, 0); self.assertIn("Accepted", lines[-1])

    def test_harness_change_is_reported(self):
        _, lines = RATCHET.check(summary(harness_changed=["scripts/stock_common.py"]), 123, HEAD, None)
        self.assertIn("scripts/stock_common.py", lines[1])

    def test_summary_of_another_run_or_commit_is_rejected(self):
        for run_id, head in ((124, HEAD), (123, "c" * 40)):
            with self.assertRaises(SystemExit): RATCHET.check(summary(), run_id, head, None)

    def test_newest_attempt_is_used(self):
        with tempfile.TemporaryDirectory() as temp:
            for attempt in (1, 2, 10):
                d = Path(temp) / f"stock-comparison-summary-{attempt}"; d.mkdir()
                (d / RATCHET.MEMBER).write_text(json.dumps({"run_attempt": attempt}))
            (Path(temp) / "unrelated").mkdir()
            self.assertEqual(RATCHET.newest_summary(Path(temp))["run_attempt"], 10)

    def test_single_artifact_extracted_in_place(self):
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp) / RATCHET.MEMBER).write_text(json.dumps({"run_attempt": 1}))
            self.assertEqual(RATCHET.newest_summary(Path(temp))["run_attempt"], 1)
            with self.assertRaises(SystemExit): RATCHET.newest_summary(Path(temp) / "missing")


if __name__ == "__main__":
    unittest.main()
