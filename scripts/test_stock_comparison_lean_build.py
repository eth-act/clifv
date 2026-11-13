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
    """Full gate runs, per run the names of its unexpired artifacts, and the conclusion of its
    assemble job (`success` unless `assemble` says otherwise; None: still running; "absent": no
    such job). `jobs_before` other jobs are listed before the assemble job."""

    def __init__(self, runs, artifacts, assemble=None, jobs_before=3):
        self.runs = {r["id"]: r for r in runs}
        self.artifacts, self.calls = artifacts, []
        self.assemble, self.jobs_before = assemble or {}, jobs_before

    def jobs(self, run_id, page):
        jobs = [{"name": f"Build wave 1 ({i}) / shard {i}", "conclusion": "success"} for i in range(self.jobs_before)]
        conclusion = self.assemble.get(run_id, "success")
        if isinstance(conclusion, list):   # several listed executions: (attempt, job id, conclusion)
            jobs += [{"name": BUILD.ASSEMBLE, "run_attempt": a, "id": i, "conclusion": c} for a, i, c in conclusion]
        elif conclusion != "absent":
            jobs.append({"name": BUILD.ASSEMBLE, "run_attempt": 1, "id": 1, "conclusion": conclusion})
        jobs.append({"name": "Axiom audits", "conclusion": "failure"})
        return {"total_count": len(jobs), "jobs": jobs[(page - 1) * 100:page * 100]}

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
        found = re.fullmatch(rf"repos/{REPO}/actions/runs/(\d+)/jobs\?filter=latest&per_page=100&page=(\d+)", path)
        if found:
            return json.dumps(self.jobs(int(found[1]), int(found[2]))).encode()
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

    def test_a_build_counts_only_after_its_assemble_job_succeeded(self):
        # review finding (CiGate4Review 2): the assemble job uploads lake-full before the list of
        # missing modules and fails after both, so a run that is still assembling, or lost its
        # runner between the uploads, looked like a complete build of the tested commit
        older = self.base
        head = self.commit({"FV/A.lean": "def a := 2\n"})
        runs = [run(5, older), run(9, head), run(10, head), run(11, head), run(12, head)]
        artifacts = {r["id"]: ["lake-full"] for r in runs}
        self.api, self.log = FakeGitHub(runs, artifacts, {9: None, 10: "failure", 11: "cancelled", 12: "absent"}), []
        found = BUILD.find(REPO, head, BUILD.Tree(self.root), api=self.api, log=self.log.append)
        self.assertEqual((found["run"], found["same_commit"], found["to_build"]), (5, False, len(CONE)))
        said = "\n".join(self.log)
        for why in ("run 9: its assemble job is not finished", "run 10: its assemble job is failure",
                    "run 11: its assemble job is cancelled", "run 12: its assemble job is not finished"):
            self.assertIn(why, said)
        # a later job's failure (the audits here) does not matter: the build is complete
        self.api = FakeGitHub(runs, artifacts, {10: "failure", 11: "failure", 12: "failure"})
        found = BUILD.find(REPO, head, BUILD.Tree(self.root), api=self.api, log=self.log.append)
        self.assertEqual((found["run"], found["same_commit"], found["to_build"]), (9, True, 0))

    def test_the_assemble_job_is_found_on_a_later_page(self):
        head = self.commit({"docs/x.md": "y\n"})
        for conclusion, expected in (("success", 5), ("failure", None)):
            self.api, self.log = FakeGitHub([run(5, head)], {5: ["lake-full"]}, {5: conclusion}, jobs_before=230), []
            found = BUILD.find(REPO, head, BUILD.Tree(self.root), api=self.api, log=self.log.append)
            self.assertEqual(found["run"], expected)
            self.assertEqual(sum("/jobs?" in call for call in self.api.calls), 3)

    def test_the_newest_execution_of_the_assemble_job_decides(self):
        # review finding (CiGate4Review round 2, 1), checked against the API: the newest attempt
        # lists a job it did not run again with its old conclusion (run 43460163729, attempt 2),
        # so a Full gate run whose audit job alone was re-run keeps its build; an assemble job
        # that was run again and failed does not
        head = self.commit({"docs/x.md": "y\n"})
        for listed, expected in (([(2, 900, "success")], 5),                        # carried over into attempt 2
                                 ([(1, 100, "success"), (2, 900, "failure")], None),
                                 ([(2, 900, "failure"), (1, 100, "success")], None),
                                 ([(1, 100, "failure"), (2, 900, "success")], 5),
                                 ([(2, 900, None)], None)):                         # running again
            self.api, self.log = FakeGitHub([run(5, head)], {5: ["lake-full"]}, {5: listed}), []
            found = BUILD.find(REPO, head, BUILD.Tree(self.root), api=self.api, log=self.log.append)
            self.assertEqual(found["run"], expected, listed)

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
        # modules. A module that reads a file while it elaborates (#1012) would be restored with
        # a stale result: a command that runs code (`#eval`, `initialize`, ...) in a module whose
        # imports, itself included, hold a reading call (the check may live in another module:
        # CiGate4Review), or an elaborator definition beside one.
        tree = BUILD.Tree(ROOT)
        reads = re.compile(r"\b(readFile|readBinFile|readDir|walkDir|readToEnd|getLine)\b|IO\.FS\.lines"
                           r"|include_str|IO\.Process\.")
        runs = re.compile(r"(?:^|\s)(#eval|run_cmd|run_elab|run_meta)\b|^\s*(?:@\[[^\]]*\]\s*)?"
                          r"(?:(?:private|protected|scoped|local|unsafe)\s+)*(initialize|builtin_initialize)\b", re.M)
        elabs = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|scoped|local|unsafe)\s+)*"
                           r"(elab|elab_rules)\b", re.M)
        text = {m: re.sub(r"--.*", "", re.sub(r"/-.*?-/", "", tree.mods[m].read_text(errors="replace"), flags=re.S))
                for m in tree.cone}
        reading = {m for m in tree.cone if reads.search(text[m])}
        self.assertGreater(len(reading), 3)   # the executables' `main`s read their inputs

        def imports_a_reader(m):
            seen, stack = set(), [m]
            while stack:
                x = stack.pop()
                if x in reading:
                    return True
                if x not in seen:
                    seen.add(x)
                    stack.extend(tree.imports[x])
            return False

        bad = sorted(m for m in tree.cone
                     if (runs.search(text[m]) and imports_a_reader(m)) or (m in reading and elabs.search(text[m])))
        self.assertEqual(bad, [])
        self.assertGreater(len(tree.cone), 300)

    def test_workflow_takes_no_cold_build(self):
        workflow = (ROOT / ".github/workflows/stock-compiler-comparison.yml").read_text()
        self.assertIn("FV_COMPARE_PREBUILT: '1'", workflow)
        self.assertIn("scripts/stock-comparison-lean-build.py --head", workflow)
        self.assertIn(".github/scripts/stock-comparison-lean.sh", workflow)
        self.assertIn("MEASURE_RESULT: ${{ needs.measure.result }}", workflow)
        # the ratchet job reports a missing measurement instead of being skipped, also after a
        # cancellation (review finding CiGate4Review 1: `!cancelled()` left it skipped at the
        # job's time limit and after a cancellation by hand)
        ratchet = workflow.split("\n  ratchet:\n")[1].split("\n  comment:\n")[0]
        self.assertIn("\n    if: ${{ always() }}\n", ratchet)
        self.assertNotIn("cancelled()", re.sub(r"(?m)^\s*#.*$", "", ratchet))
        # the two long steps end themselves long before the job limit (a job at its limit is
        # cancelled): an hour is left for downloads, caches, the partial stage and uploads
        limits = {k: int(v) for k, v in re.findall(r"(STOCK_\w+_LIMIT_S): '(\d+)'", workflow)}
        job = int(re.search(r"name: Build and compare\n(?:.*\n)*?    timeout-minutes: (\d+)", workflow)[1])
        self.assertEqual(set(limits), {"STOCK_LEAN_LIMIT_S", "STOCK_COMPARE_LIMIT_S"})
        self.assertLessEqual(sum(limits.values()) / 60 + 60, job)


LAKE_STUB = r'''#!/usr/bin/env bash
# `lake` as .github/scripts/stock-comparison-lean.sh uses it; the files in $STUB say what happens
echo "lake $*" >> "$STUB/calls"
if [[ $1 == build && $2 == --no-build ]]; then
  n=$(( $(cat "$STUB/no-build-count" 2>/dev/null || echo 0) + 1 )); echo "$n" > "$STUB/no-build-count"
  rc=$(sed -n "${n}p" "$STUB/no-build-rcs" 2>/dev/null); rc=${rc:-0}
  args=("$@")
  for (( i = 0; i < ${#args[@]}; i++ )); do
    if [[ ${args[i]} == -o && ! -e $STUB/no-outputs ]]; then echo '["hash","module.ltar"]' > "${args[i + 1]}"; fi
    if [[ ${args[i]} == -o && -e $STUB/no-outputs ]]; then : > "${args[i + 1]}"; fi
    # an up-to-date executable is restored into .lake/build/bin
    if [[ $rc == 0 && ${args[i]} == lean-* && ! -e $STUB/no-bins ]]; then
      mkdir -p .lake/build/bin; : > ".lake/build/bin/${args[i]}"; chmod +x ".lake/build/bin/${args[i]}"
    fi
  done
  exit "$rc"
elif [[ $1 == build ]]; then
  rc=$(cat "$STUB/link-rc" 2>/dev/null || echo 0)
  if [[ $rc == 0 && ! -e $STUB/no-bins ]]; then
    mkdir -p .lake/build/bin
    for exe in "${@:2}"; do : > ".lake/build/bin/$exe"; chmod +x ".lake/build/bin/$exe"; done
  fi
  exit "$rc"
elif [[ $1 == cache && $2 == stage ]]; then
  mkdir -p "$4" && cp "$3" "$4/outputs.jsonl"
fi
'''
TIMEOUT_STUB = r'''#!/usr/bin/env bash
# `timeout`: runs the command, except the scheduler, whose result is $STUB/sched-rc
echo "timeout $*" >> "$STUB/calls"
while [[ $1 == --* ]]; do shift; done
echo "$1" >> "$STUB/durations"
shift
if [[ " $* " == *" scripts/lake-serial-build.py "* ]]; then
  args=("$@")
  for (( i = 0; i < ${#args[@]}; i++ )); do
    if [[ ${args[i]} == --record ]]; then cp "$STUB/built" "${args[i + 1]}" 2>/dev/null || true; fi
    if [[ ${args[i]} == --out ]]; then mkdir -p "${args[i + 1]}"; echo "12:00:00 fail (1): FV.A" > "${args[i + 1]}/sched.log"; fi
  done
  exit "$(cat "$STUB/sched-rc" 2>/dev/null || echo 0)"
fi
exec "$@"
'''


class LeanScriptTests(unittest.TestCase):
    """.github/scripts/stock-comparison-lean.sh with `lake` and `timeout` replaced: every way it
    ends writes its stage and, on failure, one "No stock-comparison result" error."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.work = Path(self.tmp.name) / "work"
        self.stub = Path(self.tmp.name) / "stub"
        self.work.mkdir(); self.stub.mkdir()
        (self.work / "scripts").symlink_to(ROOT / "scripts")
        for name, text in (("lake", LAKE_STUB), ("timeout", TIMEOUT_STUB)):
            (self.stub / name).write_text(text)
            (self.stub / name).chmod(0o755)

    def tearDown(self):
        self.tmp.cleanup()

    def script(self, no_build=(), sched=0, built=0, link=0, limit=None, **flags):
        (self.stub / "no-build-rcs").write_text("".join(f"{rc}\n" for rc in no_build))
        (self.stub / "sched-rc").write_text(f"{sched}\n")
        (self.stub / "link-rc").write_text(f"{link}\n")
        (self.stub / "built").write_text("# module\tpeak\tseconds\n" + "".join(f"FV.M{i}\t100\t3\n" for i in range(built)))
        for flag, on in flags.items():
            if on:
                (self.stub / flag.replace("_", "-")).write_text("")
        env = {"PATH": f"{self.stub}:/usr/local/bin:/usr/bin:/bin", "STUB": str(self.stub), "HOME": str(self.work),
               "GITHUB_OUTPUT": str(self.work / "github-output")}
        if limit is not None:
            env["STOCK_LEAN_LIMIT_S"] = str(limit)
        r = subprocess.run(["bash", str(ROOT / ".github/scripts/stock-comparison-lean.sh"), "target/ci-lean", "stage"],
                           cwd=self.work, env=env, capture_output=True, text=True)
        output = dict(line.split("=", 1) for line in (self.work / "github-output").read_text().splitlines()) \
            if (self.work / "github-output").exists() else {}
        calls = (self.stub / "calls").read_text().splitlines() if (self.stub / "calls").exists() else []
        return r, output, calls

    def errors(self, r):
        return [line for line in r.stdout.splitlines() if line.startswith("::error title=No stock-comparison result::")]

    def test_everything_restored_builds_nothing(self):
        r, output, calls = self.script(no_build=[0, 0])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(output, {"stage": "full", "built": "0"})
        self.assertFalse(any("lake-serial-build.py" in call for call in calls))
        self.assertTrue((self.work / "stage/outputs.jsonl").is_file())
        self.assertEqual(self.errors(r), [])
        self.assertEqual(calls[0], "lake build --no-build " + " ".join(BUILD.EXES))

    def test_out_of_date_modules_go_through_the_scheduler_then_the_link(self):
        r, output, calls = self.script(no_build=[1, 0], built=2)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(output, {"stage": "full", "built": "2"})
        scheduler = next(call for call in calls if "lake-serial-build.py" in call)
        for wanted in ("--signal=TERM", "--budget 15G", "--heavy 12G", "--max-jobs 3", "--retry-failed",
                       *BUILD.exe_roots(ROOT)):
            self.assertIn(wanted, scheduler)
        self.assertIn("lake build " + " ".join(BUILD.EXES), calls)
        self.assertEqual(self.errors(r), [])

    def test_the_time_limit_bounds_every_long_command(self):
        r, _, _ = self.script(no_build=[1, 0], limit=7)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        durations = [int(d) for d in (self.stub / "durations").read_text().split()]
        self.assertEqual(len(durations), 2)                      # the scheduler and the link
        self.assertTrue(all(1 <= d <= 7 for d in durations), durations)
        # nothing left: still a limit (`timeout 0` would mean none)
        (self.stub / "durations").unlink(); (self.stub / "no-build-count").unlink()
        r, _, _ = self.script(no_build=[1, 0], limit=0)
        self.assertEqual([int(d) for d in (self.stub / "durations").read_text().split()], [1, 1])

    def test_scheduler_out_of_time_keeps_the_built_modules_and_fails(self):
        for rc in (124, 137):
            r, output, calls = self.script(no_build=[1, 1], sched=rc, built=5)
            self.assertEqual(r.returncode, 1, rc)
            self.assertEqual(output, {"stage": "partial", "built": "5"})
            self.assertEqual(len(self.errors(r)), 1)
            self.assertIn("did not finish within 150 minutes", self.errors(r)[0])
            self.assertTrue((self.work / "stage/outputs.jsonl").is_file())
            self.assertFalse(any(call.startswith("lake build lean-") for call in calls))   # no link
            (self.stub / "no-build-count").unlink(); (self.work / "github-output").unlink(); (self.stub / "calls").unlink()

    def test_scheduler_failure_fails_with_the_modules(self):
        r, output, _ = self.script(no_build=[1, 1], sched=1, built=1)
        self.assertEqual(r.returncode, 1)
        self.assertEqual(output["stage"], "partial")
        self.assertIn("the Lean build failed (scheduler exit 1)", self.errors(r)[0])
        self.assertIn("fail (1): FV.A", r.stdout)

    def test_link_failure_and_link_out_of_time(self):
        for rc, text in ((1, "linking the Lean executables failed (lake exit 1)"),
                         (124, "linking the Lean executables did not finish")):
            r, output, _ = self.script(no_build=[1, 1], link=rc)
            self.assertEqual(r.returncode, 1, rc)
            self.assertEqual(len(self.errors(r)), 1)
            self.assertIn(text, self.errors(r)[0])
            self.assertEqual(output["stage"], "partial")
            (self.stub / "no-build-count").unlink(); (self.work / "github-output").unlink()

    def test_missing_executable_or_stale_build_fails(self):
        r, output, _ = self.script(no_build=[0], no_bins=True)
        self.assertEqual(r.returncode, 1)
        self.assertIn(".lake/build/bin/lean-backend is missing", self.errors(r)[0])
        (self.stub / "no-bins").unlink(); (self.stub / "no-build-count").unlink(); (self.work / "github-output").unlink()
        # built and linked, yet Lake still calls an executable out of date
        r, output, _ = self.script(no_build=[1, 1])
        self.assertEqual(r.returncode, 1)
        self.assertIn("out of date right after their build", self.errors(r)[0])
        self.assertEqual(output["stage"], "partial")

    def test_nothing_to_keep_is_reported_as_no_stage(self):
        r, output, _ = self.script(no_build=[1, 1], sched=124, no_outputs=True)
        self.assertEqual(r.returncode, 1)
        self.assertEqual(output, {"stage": "none", "built": "0"})
        self.assertFalse((self.work / "stage").exists())
        self.assertEqual(len(self.errors(r)), 1)

    def test_workflow_saves_what_the_script_reports(self):
        workflow = (ROOT / ".github/workflows/stock-compiler-comparison.yml").read_text()
        self.assertIn("if: steps.lean.outputs.stage == 'full' && steps.lean-stage.outputs.cache-hit != 'true'", workflow)
        self.assertIn("if: always() && steps.lean.outputs.stage == 'partial'", workflow)
        self.assertIn('run: .github/scripts/stock-comparison-lean.sh target/ci-lean "$RUNNER_TEMP/lake-stages/own"', workflow)


if __name__ == "__main__":
    unittest.main()
