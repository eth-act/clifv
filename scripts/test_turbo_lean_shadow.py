"""Protect the experiment's verdict accounting, including failed/incomplete commands."""
import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "shadow", Path(__file__).resolve().parents[1] / ".github/scripts/turbo-lean-shadow.py")
shadow = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shadow)


class ShadowTest(unittest.TestCase):
    def test_discrepancy_truth_table(self):
        for stock, turbo in itertools.product((True, False, None), repeat=2):
            with self.subTest(stock=stock, turbo=turbo):
                expected = None if stock is None or turbo is None else stock != turbo
                self.assertEqual(shadow.comparison({"stock_ok": stock, "turbo_ok": turbo}), expected)

    def test_real_process_exit_and_timeout(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for code, verdict in ((0, True), (1, False), (124, None), (137, None), (127, None)):
                result = shadow.measure(directory, "command", [sys.executable, "-c", f"raise SystemExit({code})"], 5)
                self.assertEqual(result["ok"], verdict)
                self.assertEqual(result["exit_code"], code)
                self.assertGreaterEqual(result["wall_s"], 0)
            result = shadow.measure(directory, "timeout", [sys.executable, "-c", "import time; time.sleep(30)"], .05)
            self.assertIsNone(result["ok"])
            self.assertEqual(result["exit_code"], 124)

    def test_main_stock_failure_is_preserved_when_timing_lookup_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            record = {"event": "push", "prior_stock_job_result": "failure", "stock_ok": None,
                      "turbo_ok": None, "run_id": "42", "run_attempt": "1", "wall_s": {"stock": None}}
            shadow.write_record(directory, record)
            with patch.dict(os.environ, SHADOW_DIR=temp, GITHUB_REPOSITORY="owner/repo"), \
                 patch.object(sys, "argv", ["shadow", "stock"]), \
                 patch.object(subprocess, "check_output", side_effect=subprocess.CalledProcessError(1, "gh")):
                shadow.main()
            result = shadow.read_record(directory)
            self.assertIs(result["stock_ok"], False)
            self.assertIsNone(result["discrepancy"])
            self.assertIsNone(result["wall_s"]["stock"])

    def test_pr_policy_rejection_does_not_change_ci_discrepancy(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            record = {"base": "base-sha", "stock_ok": True, "turbo_ok": True, "pr_ok": None,
                      "commands": {}, "wall_s": {"stock": 10, "turbo": 5}}
            shadow.write_record(directory, record)
            with patch.dict(os.environ, SHADOW_DIR=temp, RUNNER_TEMP=temp), \
                 patch.object(sys, "argv", ["shadow", "pr"]), \
                 patch.object(shadow, "measure", return_value={"ok": False, "exit_code": 1, "wall_s": 1}) as run:
                shadow.main()
            self.assertIn("--disallow-statement-changes", run.call_args.args[2])
            result = shadow.read_record(directory)
            self.assertIs(result["pr_ok"], False)
            self.assertIs(result["discrepancy"], False)
            self.assertEqual(result["wall_s"], record["wall_s"])

    def test_main_stock_wall_clock_excludes_unrelated_jobs(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            record = {"event": "push", "prior_stock_job_result": "success", "stock_ok": None,
                      "turbo_ok": False, "run_id": "42", "run_attempt": "2", "wall_s": {"stock": None}}
            shadow.write_record(directory, record)
            jobs = [{"name": "Build wave 1 / shard 0", "started_at": "2026-10-31T01:00:00Z",
                     "completed_at": "2026-10-31T01:10:00Z"},
                    {"name": "Assemble build and executables", "started_at": "2026-10-31T01:11:00Z",
                     "completed_at": "2026-10-31T01:12:00Z"},
                    {"name": "Axiom audits", "started_at": "2026-10-31T01:12:00Z",
                     "completed_at": "2026-10-31T02:00:00Z"}]
            with patch.dict(os.environ, SHADOW_DIR=temp, GITHUB_REPOSITORY="owner/repo"), \
                 patch.object(sys, "argv", ["shadow", "stock"]), \
                 patch.object(subprocess, "check_output", return_value=json.dumps([{"jobs": jobs}])) as api:
                shadow.main()
            self.assertIn("/attempts/2/jobs", api.call_args.args[0][-1])
            result = shadow.read_record(directory)
            self.assertEqual(result["wall_s"]["stock"], 720)
            self.assertIs(result["discrepancy"], True)


if __name__ == "__main__":
    unittest.main()
