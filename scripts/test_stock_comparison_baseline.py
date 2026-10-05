import importlib.util
import io
import json
from pathlib import Path
import unittest
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

    def test_no_ancestor_is_unavailable(self):
        found = self.find(FakeGitHub([run(1, "1" * 40)], {1: [artifact(11, 1, {})]}), set())
        self.assertFalse(found["available"]); self.assertIn("ancestor", found["reason"])

    def test_unexpected_archives_are_rejected(self):
        with self.assertRaises(ValueError): BASELINE.read_summary(archive({}, name="../evil.json"))
        data = io.BytesIO()
        with zipfile.ZipFile(data, "w") as zf:
            zf.writestr(BASELINE.MEMBER, "{}"); zf.writestr("other.json", "{}")
        with self.assertRaises(ValueError): BASELINE.read_summary(data.getvalue())

    def test_oversized_and_misnamed_artifacts_are_ignored(self):
        github = FakeGitHub([run(1, "1" * 40)], {1: [artifact(11, 1, {}, size=BASELINE.LIMIT + 1),
            {**artifact(12, 1, {}), "name": "stock-comparison-summary-1-evil"}]})
        self.assertFalse(self.find(github, {"1" * 40})["available"])


if __name__ == "__main__":
    unittest.main()
