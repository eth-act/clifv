import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location("stock_ratchet", Path(__file__).with_name("stock-comparison-ratchet.py"))
RATCHET = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RATCHET)

HEAD = "a" * 40
LOST = ["a.clif", 0, "compile", 3, "%f"]


def summary(lost=(), gained=(), available=True, harness_changed=(), failed=False, proved=None):
    comparison = {"available": False, "failed": failed, "reason": "lookup failed" if failed else "none found"}
    if available:
        comparison = {"available": True, "run_id": 77, "run_attempt": 1, "head_sha": "b" * 40,
                      "baseline_exact_code_artifacts": 10, "gained_count": len(gained), "lost_count": len(lost),
                      "gained": list(gained), "lost": list(lost), "harness_changed": list(harness_changed),
                      "proved": proved or honest()}
    return {"run_id": 123, "head_sha": HEAD, "baseline_comparison": comparison}


def honest(lost=(), gained=()):
    return {"available": True, "baseline_proved_exact_code_artifacts": 5, "gained_count": len(gained),
            "lost_count": len(lost), "gained": list(gained), "lost": list(lost)}


class CheckTests(unittest.TestCase):
    def test_no_losses_pass(self):
        status, lines = RATCHET.check(summary(gained=[LOST]), 123, HEAD, None)
        self.assertEqual(status, 0); self.assertIn("+1 / -0", lines[0])

    def test_missing_baseline_passes_and_says_why(self):
        status, lines = RATCHET.check(summary(available=False), 123, HEAD, [])
        self.assertEqual(status, 0); self.assertIn("none found", lines[0])

    def test_failed_lookup_fails_even_with_the_label(self):
        for labels in ([], [RATCHET.LABEL], None):
            status, lines = RATCHET.check(summary(available=False, failed=True), 123, HEAD, labels)
            self.assertEqual(status, 1); self.assertIn("could not be retrieved", lines[0])
        unflagged = summary(available=False); del unflagged["baseline_comparison"]["failed"]
        self.assertEqual(RATCHET.check(unflagged, 123, HEAD, None)[0], 1)

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
        self.assertIn("scripts/stock_common.py", lines[2])

    def test_honest_losses_fail_unless_labelled(self):
        for labels in ([], None):
            status, lines = RATCHET.check(summary(proved=honest(lost=[LOST])), 123, HEAD, labels)
            self.assertEqual(status, 1)
            self.assertIn("Honest outputs that matched on main and no longer match (1):", lines)
            self.assertIn("(5 -> 4)", lines[1])
        status, lines = RATCHET.check(summary(proved=honest(lost=[LOST])), 123, HEAD, [RATCHET.LABEL])
        self.assertEqual(status, 0); self.assertIn("Accepted", lines[-1])
        status, lines = RATCHET.check(summary(proved=honest(gained=[LOST])), 123, HEAD, None)
        self.assertEqual(status, 0); self.assertIn("+1 / -0 (5 -> 6)", lines[1])

    def test_honest_baseline_before_the_metric_passes_but_a_failed_one_fails(self):
        before = {"available": False, "failed": False, "reason": "the main baseline predates the honest metric"}
        status, lines = RATCHET.check(summary(proved=before), 123, HEAD, None)
        self.assertEqual(status, 0); self.assertIn("predates", lines[1])
        for comparison in (dict(before, failed=True), {"available": False, "reason": "x"}):
            self.assertEqual(RATCHET.check(summary(proved=comparison), 123, HEAD, [RATCHET.LABEL])[0], 1)
        missing = summary(); del missing["baseline_comparison"]["proved"]
        status, lines = RATCHET.check(missing, 123, HEAD, None)
        self.assertEqual(status, 1); self.assertIn("no honest comparison", lines[-2])

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


class NoResultTests(unittest.TestCase):
    """#1018: a measuring job that did not succeed is a failed check, never a skipped one."""

    def run_main(self, measured, files=()):
        with tempfile.TemporaryDirectory() as temp:
            for attempt, data in files:
                d = Path(temp) / f"stock-comparison-summary-{attempt}"; d.mkdir()
                (d / RATCHET.MEMBER).write_text(json.dumps(data))
            step_summary = Path(temp) / "step-summary.md"
            env = {"GITHUB_RUN_ID": "123", "CI_HEAD_SHA": HEAD, "GITHUB_REPOSITORY": "eth-act/clifv",
                   "GITHUB_STEP_SUMMARY": str(step_summary)}
            if measured is not None:
                env["MEASURE_RESULT"] = measured
            out = io.StringIO()
            with mock.patch.dict(os.environ, env, clear=True), mock.patch.object(sys, "argv", ["ratchet", temp]), \
                    contextlib.redirect_stdout(out):
                try:
                    status = RATCHET.main()
                except SystemExit as stop:
                    status = stop.code
            return status, out.getvalue(), step_summary.read_text() if step_summary.exists() else ""

    def test_failed_cancelled_or_skipped_measurement_fails_with_a_message(self):
        passing = dict(summary(), run_attempt=1)
        for measured in ("failure", "cancelled", "skipped", ""):
            # an earlier attempt's passing summary does not stand for the failed attempt
            for files in ((), ((1, passing),)):
                status, out, step_summary = self.run_main(measured, files)
                self.assertEqual(status, 1, measured)
                self.assertIn("::error title=No stock-comparison result::", out)
                # review finding (CiGate4Review round 2, 2): `--failed` re-runs failed jobs and
                # their dependents, so after a cancelled measurement it re-ran the ratchet alone
                if measured == "failure":
                    self.assertIn("(`gh run rerun 123 --failed`)", out)
                else:
                    self.assertIn("(`gh run rerun 123`;", out)
                    self.assertNotIn("rerun 123 --failed", out)
                self.assertIn("No stock-comparison result", step_summary)
                self.assertIn(f"`{measured or 'unknown'}`", step_summary)

    def test_successful_measurement_is_checked_as_before(self):
        for measured in ("success", None):
            status, out, _ = self.run_main(measured, ((1, dict(summary(), run_attempt=1)),))
            self.assertEqual(status, 0); self.assertIn("+0 / -0", out)
            status, out, _ = self.run_main(measured, ((1, dict(summary(lost=[LOST]), run_attempt=1)),))
            self.assertEqual(status, 1); self.assertNotIn("No stock-comparison result", out)
            # no summary at all is a failure too, not a pass
            self.assertNotEqual(self.run_main(measured)[0], 0)



if __name__ == "__main__":
    unittest.main()
