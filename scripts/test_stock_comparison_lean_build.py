import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SPEC = importlib.util.spec_from_file_location("stock_lean_build", HERE / "stock-comparison-lean-build.py")
BUILD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)

REPO = "eth-act/clifv"
EXE_MODULES = {"lean-backend": "FVTest.Backend.Main", "lean-backend-lowering-trace": "FVTest.Backend.Lowering.Trace",
               "lean-stock-lowering-compare": "FVTest.Backend.Lowering.StockComparison",
               "lean-stock-lowering-test": "FVTest.Backend.Lowering.StockTest"}
LAKEFILE = ('name = "t"\n[[lean_lib]]\nname = "FV"\n[[lean_lib]]\nname = "FVTest"\n'
            + "".join(f'[[lean_exe]]\nname = "{e}"\nroot = "{m}"\n' for e, m in EXE_MODULES.items())
            + '[[lean_exe]]\nname = "other"\nroot = "FVTest.Other"\n')
TREE = {
    "lakefile.toml": LAKEFILE,
    "lean-toolchain": "leanprover/lean4:v4.34.1\n",
    "FV/A.lean": "def a := 1\n",
    "FV/B.lean": "import FV.A\ndef b := a\n",
    "FV/Unused.lean": "def u := 1\n",
    "FVTest/Backend/Main.lean": "import FV.B\ndef main : IO Unit := pure ()\n",
    "FVTest/Backend/Lowering/Trace.lean": "import FV.A\ndef main : IO Unit := pure ()\n",
    "FVTest/Backend/Lowering/StockComparison.lean": "import FV.A\ndef main : IO Unit := pure ()\n",
    "FVTest/Backend/Lowering/StockTest.lean": "import FV.A\ndef main : IO Unit := pure ()\n",
    "FVTest/Other.lean": "import FV.Unused\ndef main : IO Unit := pure ()\n",
    "scripts/lake-module-peaks.tsv": "FV.A\t100\t300\nFV.B\t100\t30\n",
    "docs/x.md": "x\n",
}
CONE = {"FV.A", "FV.B", *EXE_MODULES.values()}


def run(run_id, sha, event="push", branch="main", repo=REPO, path=BUILD.WORKFLOW_PATH):
    return {"id": run_id, "head_sha": sha, "event": event, "head_branch": branch, "path": path,
            "head_repository": {"full_name": repo}}


class FakeGitHub:
    """Full gate runs, and per run the names of its unexpired artifacts."""

    def __init__(self, runs, artifacts):
        self.runs = {r["id"]: r for r in runs}
        self.artifacts, self.calls = artifacts, []

    def __call__(self, path):
        self.calls.append(path)
        if "/workflows/" in path:
            sha = re.search(r"head_sha=([0-9a-f]+)", path)[1]
            return json.dumps({"workflow_runs": [r for r in self.runs.values() if r["head_sha"] == sha]}).encode()
        if path.endswith(f"/actions/artifacts?name={BUILD.ARTIFACT}&per_page=100"):
            listed = [{"name": BUILD.ARTIFACT, "expired": False, "created_at": f"2026-11-13T00:00:{i:02d}Z",
                       "workflow_run": {"id": i}}
                      for i, names in sorted(self.artifacts.items()) if BUILD.ARTIFACT in names]
            return json.dumps({"artifacts": listed}).encode()
        found = re.fullmatch(rf"repos/{REPO}/actions/runs/(\d+)(/artifacts\?per_page=100)?", path)
        if found and found[2]:
            names = self.artifacts.get(int(found[1]), [])
            return json.dumps({"artifacts": [{"name": n, "expired": False} for n in names]}).encode()
        if found:
            return json.dumps(self.runs[int(found[1])]).encode()
        raise AssertionError(path)


class Repo(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.write(TREE)
        self.git("init", "-q")
        self.base = self.commit()

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *a):
        r = subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false", *a],
                           cwd=self.root, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return r.stdout.strip()

    def write(self, files):
        for f, text in files.items():
            p = self.root / f
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)

    def commit(self, files=None):
        if files:
            self.write(files)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def find(self, runs, artifacts):
        head = self.git("rev-parse", "HEAD")
        self.api, self.log = FakeGitHub(runs, artifacts), []
        return BUILD.find(REPO, head, BUILD.Tree(self.root), api=self.api, log=self.log.append)


class ConeTests(Repo):
    def test_cone_is_the_imports_of_the_four_executables(self):
        tree = BUILD.Tree(self.root)
        self.assertEqual(tree.cone, CONE)
        self.assertEqual(BUILD.exe_roots(self.root), [EXE_MODULES[e] for e in BUILD.EXES])

    def test_a_changed_import_plans_its_importers_in_the_cone_only(self):
        self.commit({"FV/B.lean": "import FV.A\ndef b := a + 1\n", "FV/Unused.lean": "def u := 2\n"})
        tree = BUILD.Tree(self.root)
        self.assertEqual(tree.to_build(self.base), {"FV.B", "FVTest.Backend.Main"})
        self.assertEqual(tree.estimate({"FV.B", "FVTest.Backend.Main"}), BUILD.TIME_SCALE * (30 + BUILD.DEFAULT_SECS))

    def test_a_changed_toolchain_or_lake_configuration_plans_the_cone(self):
        self.commit({"lean-toolchain": "leanprover/lean4:v4.35.0\n"})
        self.assertEqual(BUILD.Tree(self.root).to_build(self.base), CONE)

    def test_a_new_executable_of_another_root_plans_nothing(self):
        self.commit({"lakefile.toml": LAKEFILE + '[[lean_exe]]\nname = "more"\nroot = "FVTest.Other"\n'})
        self.assertEqual(BUILD.Tree(self.root).to_build(self.base), set())

    def test_missing_executable_is_an_error(self):
        self.write({"lakefile.toml": LAKEFILE.replace('name = "lean-backend"\n', 'name = "renamed"\n')})
        with self.assertRaisesRegex(ValueError, "no lean_exe lean-backend"):
            BUILD.Tree(self.root)


class FindTests(Repo):
    def test_the_build_of_the_tested_commit_wins_and_ends_the_search(self):
        older = self.base
        head = self.commit({"FV/A.lean": "def a := 2\n"})
        found = self.find([run(5, older), run(9, head, event="workflow_dispatch", branch="agent/x")],
                          {5: ["lake-full"], 9: ["lake-full", "ci-plan"]})
        self.assertEqual((found["run"], found["same_commit"], found["to_build"], found["cone"]), (9, True, 0, len(CONE)))
        self.assertEqual(found["head_sha"], head)
        self.assertFalse(any("/runs/5" in call for call in self.api.calls))

    def test_without_one_the_build_that_leaves_the_least_wins(self):
        far = self.base
        near = self.commit({"FV/A.lean": "def a := 2\n"})
        self.commit({"FV/B.lean": "import FV.A\ndef b := a + 1\n"})
        found = self.find([run(5, far), run(7, near, event="workflow_dispatch", branch="agent/other")],
                          {5: ["lake-full"], 7: ["lake-full"]})
        # from run 5 everything is rebuilt (FV.A changed); from run 7 only FV.B and its importer
        self.assertEqual((found["run"], found["to_build"], found["same_commit"]), (7, 2, False))
        self.assertEqual(found["estimate_s"], round(BUILD.TIME_SCALE * (30 + BUILD.DEFAULT_SECS)))

    def test_a_change_outside_the_cone_needs_no_build(self):
        self.commit({"FV/Unused.lean": "def u := 2\n", "docs/x.md": "y\n"})
        found = self.find([run(5, self.base)], {5: ["lake-full"]})
        self.assertEqual((found["run"], found["to_build"], found["same_commit"]), (5, 0, False))

    def test_partial_expired_foreign_and_pull_request_builds_are_not_used(self):
        head = self.commit({"docs/x.md": "y\n"})
        runs = [run(1, head), run(2, head), run(3, head, event="pull_request"),
                run(4, head, repo="fork/clifv"), run(6, head, path=".github/workflows/other.yml"),
                run(8, "0" * 40)]
        found = self.find(runs, {1: ["lake-full", "lake-full-missing"], 2: ["ci-plan"], 3: ["lake-full"],
                                 4: ["lake-full"], 6: ["lake-full"], 8: ["lake-full"]})
        self.assertIsNone(found["run"])
        self.assertEqual((found["to_build"], found["cone"]), (len(CONE), len(CONE)))
        said = "\n".join(self.log)
        for why in ("run 1: a partial build", "run 2: no unexpired lake-full", "run 3: a pull_request run",
                    "run 4: a run of another repository", "run 6: not a Full gate run",
                    "run 8: its commit cannot be fetched"):
            self.assertIn(why, said)

    def test_no_run_at_all_builds_the_cone(self):
        found = self.find([], {})
        self.assertIsNone(found["run"])
        self.assertEqual(found["estimate_s"], round(BUILD.TIME_SCALE * (330 + 4 * BUILD.DEFAULT_SECS)))

    def test_only_the_newest_candidates_are_examined(self):
        shas = [self.commit({"docs/x.md": f"{i}\n"}) for i in range(BUILD.CANDIDATES + 3)]
        self.commit({"FV/A.lean": "def a := 2\n"})
        runs = [run(i + 1, sha) for i, sha in enumerate(shas)]
        found = self.find(runs, {r["id"]: ["lake-full"] for r in runs})
        examined = {int(m[1]) for call in self.api.calls if (m := re.search(r"/runs/(\d+)/artifacts", call))}
        self.assertEqual(examined, {r["id"] for r in runs[-BUILD.CANDIDATES:]})
        self.assertEqual(found["run"], runs[-1]["id"])  # all cost the same: the newest


class CommandLineTests(Repo):
    def test_prints_executables_and_roots(self):
        for what, expected in (("exes", BUILD.EXES), ("roots", [EXE_MODULES[e] for e in BUILD.EXES])):
            r = subprocess.run([sys.executable, str(HERE / "stock-comparison-lean-build.py"), "--root", str(self.root),
                                "--print", what], capture_output=True, text=True)
            self.assertEqual((r.returncode, r.stdout.split()), (0, expected), r.stderr)

    def test_a_failed_lookup_is_an_error_not_a_cold_build(self):
        # no `gh` credentials and no such repository: the lookup fails; the script must not
        # answer "no build" (which would build the whole cone)
        out = self.root / "found.json"
        env = {"PATH": "/usr/bin:/bin", "GITHUB_REPOSITORY": "eth-act/does-not-exist", "GH_TOKEN": "invalid",
               "HOME": str(self.root), "GH_HOST": "invalid.invalid"}
        r = subprocess.run([sys.executable, str(HERE / "stock-comparison-lean-build.py"), "--root", str(self.root),
                            "--head", self.base, "--out", str(out)], capture_output=True, text=True, env=env)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("::error title=No stock-comparison result::", r.stdout)
        self.assertFalse(out.exists())


class RepositoryTests(unittest.TestCase):
    """The real tree: the lists and limits the workflow relies on."""

    def test_executables_are_the_ones_the_comparison_runs(self):
        script = (ROOT / "scripts/stock-compiler-comparison.sh").read_text()
        listed = re.search(r"^LEAN_EXES=\(([^)]*)\)$", script, re.M)[1].split()
        self.assertEqual(sorted(listed), sorted(BUILD.EXES))
        self.assertEqual(len(re.findall(r"lake build (?:--no-build )?\"\$\{LEAN_EXES\[@\]\}\"", script)), 2)
        self.assertNotIn("lake build lean-", script)

    def test_no_module_of_the_cone_reads_a_file_while_it_elaborates(self):
        # Any Full gate build may be the starting point because Lake traces every input of these
        # modules. A module that reads a file while it elaborates (#1012: `#eval`, `initialize`,
        # an elaborator calling IO.FS) would be restored with a stale result.
        tree = BUILD.Tree(ROOT)
        reads = re.compile(r"IO\.FS\.(readFile|readBinFile|lines|readDir)|\.readDir\b|include_str")
        elaborates = re.compile(r"^\s*(#eval|run_cmd|run_elab|run_meta|initialize|builtin_initialize)\b", re.M)
        bad = sorted(m for m in tree.cone
                     if reads.search(text := tree.mods[m].read_text(errors="replace")) and elaborates.search(text))
        self.assertEqual(bad, [])
        self.assertGreater(len(tree.cone), 300)

    def test_workflow_takes_no_cold_build(self):
        workflow = (ROOT / ".github/workflows/stock-compiler-comparison.yml").read_text()
        self.assertIn("FV_COMPARE_PREBUILT: '1'", workflow)
        self.assertIn("scripts/stock-comparison-lean-build.py --head", workflow)
        self.assertIn(".github/scripts/stock-comparison-lean.sh", workflow)
        self.assertIn("MEASURE_RESULT: ${{ needs.measure.result }}", workflow)
        # the ratchet job reports a missing measurement instead of being skipped
        ratchet = workflow.split("\n  ratchet:\n")[1].split("\n  comment:\n")[0]
        self.assertIn("if: ${{ !cancelled() }}", ratchet)
        # the two long steps end themselves before the job limit (a job at its limit is cancelled)
        limits = {k: int(v) for k, v in re.findall(r"(STOCK_\w+_LIMIT_S): '(\d+)'", workflow)}
        job = int(re.search(r"name: Build and compare\n(?:.*\n)*?    timeout-minutes: (\d+)", workflow)[1])
        self.assertEqual(set(limits), {"STOCK_LEAN_LIMIT_S", "STOCK_COMPARE_LIMIT_S"})
        self.assertLessEqual(sum(limits.values()) / 60 + 20, job)


if __name__ == "__main__":
    unittest.main()
