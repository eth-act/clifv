import importlib.util, json, pathlib, subprocess, sys, tempfile, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("ci_build_plan", HERE / "ci-build-plan.py")
cbp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cbp)

LAKEFILE = 'name = "t"\n[[lean_lib]]\nname = "FV"\n[[lean_lib]]\nname = "FVTest"\n'
# the shape of FVTest/Isle/Interp.lean: a check that reads a file while the module elaborates
INTERP = 'import FV.A\n#eval show IO Unit from do\n  let _ ← IO.FS.readFile "FVTest/Isle/oracle/cases.trace"\n'
TREE = {
    "lakefile.toml": LAKEFILE,
    "lean-toolchain": "leanprover/lean4:v4.34.1\n",
    "FV/A.lean": "def a := 1\n",
    "FV/B.lean": "import FV.A\ndef b := a\n",
    "FVTest/Isle/Interp.lean": INTERP,
    "FVTest/Isle/oracle/cases.trace": "case 1 -> 2\n",
    "corpus/clif/x.clif": "function %x() {}\n",
    "scripts/fetch-third-party.sh": "WASMTIME_COMMIT=aaaa\n",
    "scripts/gate-expected-counts.txt": "fv-demo 2 1372 1372\n",
    "docs/TO-PROVE.md": "x\n",
    "LEARNINGS.md": "x\n",
}


class UntracedInputs(unittest.TestCase):
    def test_directories_no_module_build_reads(self):
        ok = [".github/workflows/full-gate.yml", "docs/a/b.md", "crate-proofs/Crates/AArith.lean",
              "rust/crates/cargo-fv/src/bincheck.rs", "examples/survey/Cargo.lock",
              "scripts/gate-line-check.py", "scripts/audit/e2e.lean", "LEARNINGS.md", "AGENTS.md",
              "docs/with space.md"]
        self.assertEqual(cbp.untraced_inputs(ok), [])

    def test_possible_inputs(self):
        bad = ["FVTest/Isle/oracle/cases.trace", "corpus/clif/x.clif", "scripts/fetch-third-party.sh",
               "third_party/NOTICE-lnsym.md", "FV/README.md", "rust-toolchain.toml", ".gitattributes",
               "FV/Removed.lean", "docsx/a.md", "tools/x.py"]
        self.assertEqual(cbp.untraced_inputs(bad), sorted(bad))


class Plan(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
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

    def commit(self):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c")
        return self.git("rev-parse", "HEAD")

    def plan(self, *extra):
        out = self.root / "plan.json"
        out.unlink(missing_ok=True)
        r = subprocess.run([sys.executable, str(HERE / "ci-build-plan.py"), "--root", str(self.root), "--base", self.base,
                            "--out", str(out), *extra, "FV", "FVTest"], capture_output=True, text=True)
        planned = None
        if out.exists():
            planned = sorted(m for w in json.loads(out.read_text())["waves"] for s in w for m in s["modules"])
        return r, planned

    def test_fixture_alone_differs_from_a_named_baseline(self):
        # review finding (CiGate3Review 1): a branch stacked on a PR's head changes only the file
        # FVTest.Isle.Interp reads while it elaborates; with that PR's run as `base-run` the plan
        # held no module, and the cached result of the old fixture stood for the new one
        self.write({"FVTest/Isle/oracle/cases.trace": "case 1 -> 3\n"})
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("FVTest/Isle/oracle/cases.trace", r.stderr)
        self.assertIn("run without base-run", r.stderr)
        self.assertIsNone(planned)

    def test_every_untraced_input_is_refused(self):
        for f, text in (("corpus/clif/x.clif", "function %y() {}\n"), ("scripts/fetch-third-party.sh", "WASMTIME_COMMIT=bbbb\n"),
                        ("FVTest/Isle/oracle/new file.trace", "x\n"), ("FVTest/Isle/oracle/caf\u00e9.trace", "x\n")):
            self.write({f: text})
            self.commit()
            r, planned = self.plan("--explicit-base")
            self.assertNotEqual(r.returncode, 0, f)
            self.assertIn(f, r.stderr)
            self.assertIsNone(planned, f)
            self.base = self.git("rev-parse", "HEAD")

    def test_deleted_fixture_is_refused(self):
        (self.root / "FVTest/Isle/oracle/cases.trace").unlink()
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertNotEqual(r.returncode, 0)
        self.assertIsNone(planned)

    def test_fixture_moved_into_an_allowed_directory(self):
        # review finding (CiGate3Review 2): git reported an exact rename by its new name only, so
        # the fixture moved to scripts/ looked like a new script; Interp still reads the old path
        (self.root / "FVTest/Isle/oracle/cases.trace").rename(self.root / "scripts/cases.trace")
        self.commit()
        self.assertEqual(self.git("diff", "--name-only", self.base, "HEAD"), "scripts/cases.trace")
        r, planned = self.plan("--explicit-base")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("FVTest/Isle/oracle/cases.trace", r.stderr)
        self.assertIsNone(planned)

    def test_fixture_replaced_by_a_link_to_a_module(self):
        # review finding (CiGate3Review 3): the changed path was followed before it was classified,
        # so a fixture that became a symbolic link to a module source counted as that module
        self.write({"FVTest/Unrelated.lean": "def u := 1\n"})
        (self.root / "FVTest/Isle/oracle/cases.trace").unlink()
        (self.root / "FVTest/Isle/oracle/cases.trace").symlink_to("../../Unrelated.lean")
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("FVTest/Isle/oracle/cases.trace", r.stderr)
        self.assertIsNone(planned)
        r, planned = self.plan()   # the automatic baseline: the module the link leads to, as before
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, ["FVTest.Unrelated"])

    def test_allowed_file_read_through_a_link(self):
        # the baseline already holds a link from a fixture's place into docs/ (file or directory):
        # a change behind it is a change of what the module reads
        (self.root / "FVTest/Isle/oracle/cases.trace").unlink()
        (self.root / "FVTest/Isle/oracle/cases.trace").symlink_to("../../../docs/cases.trace")
        (self.root / "FVTest/Isle/more").symlink_to("../../docs/more")
        self.write({"docs/cases.trace": "case 1 -> 2\n", "docs/more/a/b.trace": "x\n", "docs/other.md": "x\n"})
        self.base = self.commit()
        for f in ("docs/cases.trace", "docs/more/a/b.trace"):
            self.write({f: "changed\n", "docs/other.md": f})
            self.commit()
            r, planned = self.plan("--explicit-base")
            self.assertNotEqual(r.returncode, 0, f)
            self.assertIn(f + " (through FVTest/Isle/", r.stderr)
            self.assertNotIn("docs/other.md", r.stderr)
            self.assertIsNone(planned, f)
            self.base = self.git("rev-parse", "HEAD")
        self.write({"docs/other.md": "y\n"})
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, [])

    def test_removed_or_renamed_module_is_refused(self):
        # its old path is no module source any more: a named baseline does not guess what read it
        (self.root / "FV/B.lean").rename(self.root / "FV/C.lean")
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("FV/B.lean", r.stderr)
        r, planned = self.plan()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, ["FV.C"])

    def test_tooling_and_documents_plan_nothing(self):
        # the stacked gate-tooling branch: workflow, scripts, Rust tool, documents, crate proofs
        self.write({".github/workflows/full-gate.yml": "on: push\n", "scripts/gate-expected-counts.txt": "fv-demo 2 1400 1400\n",
                    "rust/crates/cargo-fv/src/bincheck.rs": "fn f() {}\n", "docs/TO-PROVE.md": "y\n", "LEARNINGS.md": "y\n",
                    "crate-proofs/Crates/AArith.lean": "theorem t : True := trivial\n", "docs/caf\u00e9 notes.md": "x\n"})
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, [])

    def test_module_sources_are_planned_with_their_importers(self):
        self.write({"FV/A.lean": "def a := 2\n", "docs/TO-PROVE.md": "y\n"})
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, ["FV.A", "FV.B", "FVTest.Isle.Interp"])

    def test_global_input_plans_everything(self):
        self.write({"lean-toolchain": "leanprover/lean4:v4.35.0\n", "FVTest/Isle/oracle/cases.trace": "case 1 -> 3\n"})
        self.commit()
        r, planned = self.plan("--explicit-base")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, ["FV.A", "FV.B", "FVTest.Isle.Interp"])

    def test_unknown_commit_is_no_plan_on_a_named_baseline(self):
        self.base = "0" * 40
        r, planned = self.plan("--explicit-base")
        self.assertNotEqual(r.returncode, 0)
        self.assertIsNone(planned)
        r, planned = self.plan()   # the automatic baseline: everything, as before
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, ["FV.A", "FV.B", "FVTest.Isle.Interp"])

    def test_explicit_needs_a_base(self):
        r = subprocess.run([sys.executable, str(HERE / "ci-build-plan.py"), "--root", str(self.root), "--explicit-base",
                            "--out", str(self.root / "plan.json"), "FV", "FVTest"], capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)
        self.assertFalse((self.root / "plan.json").exists())

    def test_automatic_baseline_is_unchanged(self):
        # without --explicit-base the planner does what it did: module sources only
        self.write({"FV/B.lean": "import FV.A\ndef b := a + 1\n", "docs/with space.md": "x\n"})
        self.commit()
        r, planned = self.plan()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(planned, ["FV.B"])


class Workflow(unittest.TestCase):
    def test_plan_step_fails_with_the_planner(self):
        # the step pipes the planner into tee: without pipefail its refusal left the step green
        text = (HERE.parent / ".github/workflows/full-gate.yml").read_text()
        step = text[text.index("      - name: Plan\n"):]
        step = step[:step.index("      - uses:")]
        run = step[step.index("        run: |\n"):]
        self.assertLess(run.index("set -o pipefail"), run.index("scripts/ci-build-plan.py"))
        self.assertIn("${EXPLICIT:+--explicit-base}", run)
        self.assertIn("EXPLICIT: ${{ steps.base.outputs.run && inputs.base-run }}", step)


if __name__ == "__main__":
    unittest.main()
