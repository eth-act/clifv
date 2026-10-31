"""Protect verdict provenance and accounting for failed/incomplete shadow runs."""
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
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.event = self.directory / "event.json"
        self.trigger = {"id": 42, "run_attempt": 2, "head_sha": "a" * 40}
        self.event.write_text(json.dumps({"workflow_run": self.trigger}))
        self.env = patch.dict(os.environ, SHADOW_DIR=self.temp.name, RUNNER_TEMP=self.temp.name,
                              GITHUB_REPOSITORY="owner/repo", GITHUB_EVENT_PATH=str(self.event),
                              GITHUB_EVENT_NAME="workflow_run", GITHUB_RUN_ID="99",
                              GITHUB_RUN_ATTEMPT="1", TURBO_SHA="b" * 40,
                              GITHUB_OUTPUT=str(self.directory / "output"))
        self.env.start()
        self.addCleanup(self.env.stop)
        self.run_action("init")
        self.run_info = {"name": "Full gate", "path": ".github/workflows/full-gate.yml",
                         "head_repository": {"full_name": "owner/repo"}, "event": "push",
                         "status": "completed", "conclusion": "success", "head_sha": "a" * 40,
                         "head_branch": "main", "run_attempt": 3}
        self.jobs = [self.job("Plan"), self.job("Build wave 1 / shard 0"),
                     self.job("Assemble build and executables"), self.job("Axiom audits")]

    @staticmethod
    def job(name, conclusion="success"):
        return {"id": 1, "name": name, "conclusion": conclusion,
                "started_at": "2026-10-31T01:00:00Z", "completed_at": "2026-10-31T01:10:00Z"}

    def run_action(self, action):
        with patch.object(sys, "argv", ["shadow", action]):
            shadow.main()
        return shadow.read_record(self.directory)

    def read_stock(self):
        with patch.object(shadow, "api", side_effect=[self.run_info, self.run_info, [{"jobs": self.jobs}]]) as api:
            result = self.run_action("stock")
        self.assertIn("/attempts/2", api.call_args_list[1].args[0])
        return result

    def test_init_has_no_invented_verdict_or_source(self):
        record = shadow.read_record(self.directory)
        for field in ("stock_ok", "stock_source", "turbo_ok", "discrepancy", "base", "commit"):
            self.assertIsNone(record[field])
        self.assertFalse(record["eligible"])

    def test_discrepancy_truth_table(self):
        for stock, turbo in itertools.product((True, False, None), repeat=2):
            with self.subTest(stock=stock, turbo=turbo):
                expected = None if stock is None or turbo is None else stock != turbo
                self.assertEqual(shadow.comparison({"stock_ok": stock, "turbo_ok": turbo}), expected)

    def test_real_process_exit_and_timeout(self):
        for code, verdict in ((0, True), (1, False), (124, None), (137, None), (127, None)):
            result = shadow.measure(self.directory, "command", [sys.executable, "-c", f"raise SystemExit({code})"], 5)
            self.assertEqual(result["ok"], verdict)
            self.assertEqual(result["exit_code"], code)
            self.assertGreaterEqual(result["wall_s"], 0)
        result = shadow.measure(self.directory, "timeout", [sys.executable, "-c", "import time; time.sleep(30)"], .05)
        self.assertIsNone(result["ok"])
        self.assertEqual(result["exit_code"], 124)

    def test_memcap_timeout_uses_foreground_and_telemetry_off(self):
        with patch.object(subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as run:
            shadow.measure(self.directory, "ci", ["scripts/memcap.sh", "turbo-lean"], 900)
        self.assertIn("--foreground", run.call_args.args[0])
        self.assertEqual(run.call_args.kwargs["env"]["TURBO_LEAN_TELEMETRY"], "off")

    def test_job_api_paginates_without_losing_conclusions(self):
        pages = [{"jobs": [self.job("Build wave 1 / shard 0")] * 100},
                 {"jobs": [self.job("Assemble build and executables", "failure")]}]
        with patch.object(subprocess, "check_output", side_effect=[json.dumps(p) for p in pages]) as run:
            result = shadow.api("repos/owner/repo/actions/runs/42/attempts/2/jobs?per_page=100", True)
        self.assertEqual(result, pages)
        self.assertIn("&page=2", run.call_args.args[0][-1])

    def test_actual_job_success_and_original_attempt(self):
        record = self.read_stock()
        self.assertTrue(record["stock_ok"])
        self.assertTrue(record["eligible"])
        self.assertEqual(record["stock_run_attempt"], 2)
        self.assertEqual(record["stock_run_id"], "42")
        self.assertEqual(record["commit"], "a" * 40)
        self.assertEqual(len(record["stock_jobs"]), 3)

    def test_failed_wave_and_skipped_assemble_are_failed_stock(self):
        self.jobs[1]["conclusion"] = "failure"
        self.jobs[2]["conclusion"] = "skipped"
        self.run_info["conclusion"] = "failure"
        record = self.read_stock()
        self.assertIs(record["stock_ok"], False)
        self.assertFalse(record["eligible"])
        self.assertIsNone(record["turbo_ok"])
        self.assertIsNone(record["discrepancy"])

    def test_cancelled_or_missing_assemble_is_unknown(self):
        for conclusion in ("cancelled", "skipped", None):
            with self.subTest(conclusion=conclusion):
                self.run_action("init")
                self.jobs[2]["conclusion"] = conclusion
                record = self.read_stock()
                self.assertIsNone(record["stock_ok"])
                self.assertFalse(record["eligible"])
        self.run_action("init")
        self.jobs.pop(2)
        self.assertIsNone(self.read_stock()["stock_ok"])

    def test_failed_plan_or_trigger_never_runs_shadow_even_with_green_stock(self):
        for field in ("plan", "run"):
            with self.subTest(field=field):
                self.run_action("init")
                self.jobs[0]["conclusion"] = "failure" if field == "plan" else "success"
                self.run_info["conclusion"] = "failure" if field == "run" else "success"
                record = self.read_stock()
                self.assertTrue(record["stock_ok"])
                self.assertFalse(record["eligible"])

    def test_lookup_failure_stays_incomplete(self):
        with patch.object(shadow, "api", side_effect=subprocess.CalledProcessError(1, "gh")):
            record = self.run_action("stock")
        self.assertIsNone(record["stock_ok"])
        self.assertIsNone(record["stock_source"])
        self.assertFalse(record["eligible"])
        self.assertIn("stock_lookup_error", record)

    def test_rejects_fork_pr_other_workflow_and_non_main_automatic_sources(self):
        for key, value in (("head_repository", {"full_name": "fork/repo"}),
                           ("event", "pull_request"), ("name", "Stock compiler comparison"),
                           ("path", ".github/workflows/other.yml"), ("head_branch", "feature"),
                           ("status", "in_progress"), ("head_sha", "c" * 40)):
            with self.subTest(key=key):
                self.run_action("init")
                run = {**self.run_info, key: value}
                with patch.object(shadow, "api", side_effect=[run, run]):
                    record = self.run_action("stock")
                self.assertIsNone(record["stock_source"])
                self.assertIsNone(record["stock_ok"])
                self.assertFalse(record["eligible"])

    def test_dispatch_allows_opt_in_same_repo_branch_and_uses_its_attempt(self):
        with patch.dict(os.environ, GITHUB_EVENT_NAME="workflow_dispatch", STOCK_RUN_ID="42"):
            self.run_action("init")
            self.run_info.update(head_branch="pr-experiment", event="workflow_dispatch")
            with patch.object(shadow, "api", side_effect=[self.run_info, self.run_info, [{"jobs": self.jobs}]]) as api:
                record = self.run_action("stock")
            self.assertTrue(record["eligible"])
            self.assertEqual(record["stock_branch"], "pr-experiment")
            self.assertIn("/attempts/3/jobs", api.call_args.args[0])

    def test_invalid_dispatch_id_never_reaches_api(self):
        with patch.dict(os.environ, GITHUB_EVENT_NAME="workflow_dispatch", STOCK_RUN_ID="42/other"), \
             patch.object(shadow, "api") as api:
            self.run_action("init")
            record = self.run_action("stock")
        api.assert_not_called()
        self.assertFalse(record["eligible"])

    def test_stock_wall_clock_excludes_unrelated_jobs(self):
        self.jobs[1].update(started_at="2026-10-31T01:00:00Z", completed_at="2026-10-31T01:10:00Z")
        self.jobs[2].update(started_at="2026-10-31T01:11:00Z", completed_at="2026-10-31T01:12:00Z")
        self.jobs[3]["completed_at"] = "2026-10-31T02:00:00Z"
        self.assertEqual(self.read_stock()["wall_s"]["stock"], 720)

    def test_ineligible_stock_prevents_verifier(self):
        with patch.object(shadow, "measure") as measure:
            with self.assertRaisesRegex(ValueError, "successful stock provenance"):
                self.run_action("ci")
        measure.assert_not_called()

    def test_pr_policy_rejection_does_not_change_ci_discrepancy(self):
        record = self.read_stock()
        record.update(base="c" * 40, turbo_ok=True)
        record["wall_s"]["turbo"] = 5
        shadow.write_record(self.directory, record)
        with patch.object(shadow, "measure", return_value={"ok": False, "exit_code": 1, "wall_s": 1}) as run:
            result = self.run_action("pr")
        self.assertIn("--disallow-statement-changes", run.call_args.args[2])
        self.assertIs(result["pr_ok"], False)
        self.assertIs(result["discrepancy"], False)
        self.assertEqual(result["wall_s"], record["wall_s"])


if __name__ == "__main__":
    unittest.main()
