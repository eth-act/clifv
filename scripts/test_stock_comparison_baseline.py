import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock
import zipfile

SPEC = importlib.util.spec_from_file_location("stock_baseline", Path(__file__).with_name("stock-comparison-baseline.py"))
BASELINE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASELINE)

REPO = "eth-act/clifv"
HEAD = "f" * 40


def archive(summary, name=BASELINE.MEMBER):
    data = io.BytesIO()
    with zipfile.ZipFile(data, "w") as zf:
        zf.writestr(name, json.dumps(summary))
    return data.getvalue()


def run(run_id, sha, event="push", branch="main"):
    return {"id": run_id, "head_sha": sha, "event": event, "head_branch": branch}


class FakeGitHub:
    """Runs (newest last is fine: find() sorts), their artifacts, and archive contents."""
    def __init__(self, runs, artifacts):
        self.runs, self.artifacts, self.calls = runs, artifacts, []

    def __call__(self, path):
        self.calls.append(path)
        if "/workflows/" in path:
            return json.dumps({"workflow_runs": self.runs}).encode()
        if path.endswith("/zip"):
            artifact_id = int(path.split("/")[-2])
            return next(a["_zip"] for listed in self.artifacts.values() for a in listed if a["id"] == artifact_id)
        run_id = int(path.split("/runs/")[1].split("/")[0])
        listed = [{k: v for k, v in a.items() if k != "_zip"} for a in self.artifacts.get(run_id, [])]
        return json.dumps({"artifacts": listed}).encode()


def artifact(artifact_id, attempt, summary, expired=False, size=512):
    return {"id": artifact_id, "name": f"stock-comparison-summary-{attempt}", "expired": expired,
            "size_in_bytes": size, "_zip": archive(summary)}


class FindTests(unittest.TestCase):
    def find(self, github, ancestors, current=999):
        return BASELINE.find(REPO, HEAD, current, api=github, ancestor=lambda sha, head: sha in ancestors)

    def test_newest_ancestor_with_summary_and_its_newest_attempt(self):
        github = FakeGitHub(
            [run(1, "1" * 40), run(2, "2" * 40), run(3, "3" * 40)],
            {1: [artifact(11, 1, {"n": 1})],
             2: [artifact(21, 1, {"n": 21}), artifact(22, 2, {"n": 22})],
             3: [artifact(31, 1, {"n": 3})]})
        found = self.find(github, {"1" * 40, "2" * 40})  # run 3 is on main but newer than the branch
        self.assertEqual((found["run_id"], found["run_attempt"], found["head_sha"], found["summary"]),
                         (2, 2, "2" * 40, {"n": 22}))

    def test_current_run_other_events_and_runs_without_summary_are_skipped(self):
        github = FakeGitHub(
            [run(1, "1" * 40), run(2, "2" * 40), run(3, "3" * 40, event="pull_request"), run(999, "4" * 40)],
            {1: [artifact(11, 1, {"n": 1})], 2: [artifact(21, 1, {"n": 2}, expired=True)],
             3: [artifact(31, 1, {"n": 3})], 999: [artifact(41, 1, {"n": 4})]})
        found = self.find(github, {"1" * 40, "2" * 40, "3" * 40, "4" * 40})
        self.assertEqual(found["run_id"], 1)

    def test_no_ancestor_is_a_missing_baseline_not_a_failure(self):
        found = self.find(FakeGitHub([run(1, "1" * 40)], {1: [artifact(11, 1, {})]}), set())
        self.assertFalse(found["available"]); self.assertFalse(found["failed"])
        self.assertIn("ancestor", found["reason"])

    def test_unexpected_archives_are_rejected(self):
        with self.assertRaises(ValueError): BASELINE.read_summary(archive({}, name="../evil.json"))
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as zf:
            zf.writestr(BASELINE.MEMBER, "{}"); zf.writestr("other.json", "{}")
        with self.assertRaises(ValueError): BASELINE.read_summary(data.getvalue())

    def test_misnamed_artifacts_are_ignored(self):
        github = FakeGitHub([run(1, "1" * 40)], {1: [{**artifact(12, 1, {}), "name": "stock-comparison-summary-1-evil"}]})
        self.assertFalse(self.find(github, {"1" * 40})["failed"])

    def test_unreadable_baselines_raise(self):
        oversized = FakeGitHub([run(1, "1" * 40)], {1: [artifact(11, 1, {}, size=BASELINE.LIMIT + 1)]})
        with self.assertRaises(ValueError): self.find(oversized, {"1" * 40})
        damaged = FakeGitHub([run(1, "1" * 40)], {1: [{**artifact(11, 1, {}), "_zip": b"not a zip"}]})
        with self.assertRaises(zipfile.BadZipFile): self.find(damaged, {"1" * 40})


class MainTests(unittest.TestCase):
    """A lookup that fails is recorded as failed, and the script still exits 0."""
    def lookup(self, error):
        with tempfile.TemporaryDirectory() as temp, \
                mock.patch.dict(os.environ, {"GITHUB_REPOSITORY": REPO, "GITHUB_RUN_ID": "5"}), \
                mock.patch.object(BASELINE, "find", side_effect=error), \
                mock.patch("sys.argv", ["baseline", "--head", HEAD, "--out", f"{temp}/b.json"]), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(BASELINE.main(), 0)
            return json.loads(Path(temp, "b.json").read_text())

    def test_api_and_archive_failures_are_failed_lookups(self):
        for error in (subprocess.CalledProcessError(1, ["gh", "api", "x"], stderr=b"HTTP 502"),
                      zipfile.BadZipFile("File is not a zip file"), KeyError("workflow_runs")):
            found = self.lookup(error)
            self.assertEqual((found["available"], found["failed"]), (False, True))
            self.assertIn(type(error).__name__, found["reason"])


class AncestorTests(unittest.TestCase):
    def test_unknown_commit_is_not_an_ancestor_unless_the_clone_is_shallow(self):
        with tempfile.TemporaryDirectory() as temp:
            git = lambda *a, cwd=temp: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a],
                                                      cwd=cwd, check=True, capture_output=True, text=True).stdout
            source = Path(temp, "source"); source.mkdir()
            git("init", "-q", cwd=source)
            for n in (1, 2):
                git("commit", "-q", "--allow-empty", "-m", str(n), cwd=source)
            git("clone", "-q", "--depth", "1", source.as_uri(), "clone")
            head = git("rev-parse", "HEAD", cwd=Path(temp, "clone")).strip()
            cwd = os.getcwd()
            try:
                os.chdir(source)  # full history: a rewritten main's old commit is simply not an ancestor
                self.assertFalse(BASELINE.is_ancestor("1" * 40, head))
                os.chdir(Path(temp, "clone"))
                self.assertTrue(BASELINE.is_ancestor(head, head))
                with self.assertRaises(ValueError): BASELINE.is_ancestor("1" * 40, head)
            finally:
                os.chdir(cwd)


if __name__ == "__main__":
    unittest.main()
