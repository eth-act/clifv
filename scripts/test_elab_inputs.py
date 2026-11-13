import contextlib, importlib.util, io, pathlib, re, subprocess, tempfile, types, unittest

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location("elab_inputs", HERE / "elab-inputs.py")
ei = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ei)


def tree(files):
    """(mods, imports) of a made-up library: {module: source text}."""
    tmp = tempfile.TemporaryDirectory()
    mods, imports = {}, {}
    for m, text in files.items():
        p = pathlib.Path(tmp.name) / (m.replace(".", "/") + ".lean")
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        mods[m] = p
        imports[m] = [i for i in re.findall(r"^import (\S+)", text, re.M) if i in files]
    return tmp, mods, imports


READ = 'def check : IO Unit := do\n  let _ ← IO.FS.readFile "fixtures/a.trace"\n'


class Candidates(unittest.TestCase):
    def flagged(self, files, not_readers=()):
        tmp, mods, imports = tree(files)
        with tmp:
            return ei.candidates(mods, imports, not_readers)

    def test_eval_of_a_reading_check(self):
        self.assertEqual(self.flagged({"T.A": READ + "#eval check\n", "T.B": "import T.A\ndef b := 1\n"}), {"T.A"})

    def test_the_read_may_be_in_an_import(self):
        # T.Lib only defines the check; T.Use runs it while it elaborates
        files = {"T.Lib": READ, "T.Mid": "import T.Lib\n", "T.Use": "import T.Mid\n#eval check\n",
                 "T.Pure": "#eval 1 + 1\n"}
        self.assertEqual(self.flagged(files), {"T.Use"})

    def test_every_command_that_runs_code(self):
        for command in ("#eval check", "run_cmd check", "run_elab check", "run_meta check",
                        "initialize check", "builtin_initialize check", "initialize x : Nat ← check",
                        "@[init] private initialize check", "#guard_msgs in #eval check",
                        "  #eval check", "unsafe initialize check",
                        # review finding (CiGate4Review2 3): a tactic block runs code too
                        "example : True := by run_tac check", "example : True := by\n  run_tac (check)\n  trivial",
                        "example : True := by (run_tac check)"):
            self.assertEqual(self.flagged({"T.A": READ + command + "\n"}), {"T.A"}, command)

    def test_other_readers(self):
        for call in ('IO.FS.readBinFile "x"', '(System.FilePath.mk "d").readDir', 'IO.FS.lines "x"',
                     '(System.FilePath.mk "d").walkDir', 'include_str "x"', 'IO.Process.output { cmd := "x" }',
                     'IO.Process.run { cmd := "x" }', 'h.readToEnd', 'h.getLine',
                     # review finding (CiGate4Review2 3): existence, metadata, handles, the environment
                     '(System.FilePath.mk "fixture").pathExists', '(System.FilePath.mk "d").isDir',
                     '(System.FilePath.mk "f").metadata', 'IO.FS.realPath "f"', '(System.FilePath.mk "f").realPath',
                     'IO.getEnv "FIXTURE"', 'IO.FS.Handle.mk "f" .read', 'IO.FS.withFile "f" .read fun h => h.read 10',
                     'IO.currentDir', 'IO.getStdin'):
            self.assertEqual(self.flagged({"T.A": f"def check : IO Unit := do\n  let _ ← {call}\n#eval check\n"}),
                             {"T.A"}, call)
            # the reading helper in an import, the command in the importer
            self.assertEqual(self.flagged({"T.Lib": f"def check : IO Unit := do\n  let _ ← {call}\n",
                                           "T.Use": "import T.Lib\nexample : True := by run_tac check\n"}), {"T.Use"}, call)

    def test_leans_own_environment_is_not_an_input(self):
        # `getEnv` (the declarations elaborated so far) is in most elaborators
        files = {"T.A": 'elab "find_it" : tactic => do\n  let env ← getEnv\n  pure ()\n#eval 1\n'}
        self.assertEqual(self.flagged(files), set())

    def test_an_elaborator_that_reads(self):
        self.assertEqual(self.flagged({"T.Tac": READ + 'elab "load_it" : tactic => do\n  check\n'}), {"T.Tac"})

    def test_syntax_runs_where_it_is_used(self):
        # review finding (CiGate4Review2 2): the module that defines a macro or an elaborator is
        # elaborated without running it; the check runs in the modules that use the syntax
        macro = {"T.Lib": READ, "T.Cmd": 'import T.Lib\nmacro "#check_fixture" : command => `(#eval check)\n',
                 "T.Use": "import T.Cmd\n#check_fixture\n", "T.Far": "import T.Use\ndef far := 1\n",
                 "T.Other": "import T.Lib\ndef other := 1\n"}
        self.assertEqual(self.flagged(macro), {"T.Cmd", "T.Use", "T.Far"})
        elab = {"T.Lib": READ, "T.Tac": 'import T.Lib\nelab "load_it" : tactic => do\n  check\n',
                "T.Use": "import T.Tac\nexample : True := by\n  load_it\n  trivial\n"}
        self.assertEqual(self.flagged(elab), {"T.Tac", "T.Use"})
        rules = {"T.Lib": READ, "T.Syn": 'import T.Lib\nsyntax "load_it" : tactic\n',
                 "T.Tac": "import T.Syn\nelab_rules : tactic | `(tactic| load_it) => check\n",
                 "T.Use": "import T.Tac\nexample : True := by load_it\n"}
        self.assertEqual(self.flagged(rules), {"T.Tac", "T.Use"})

    def test_a_pure_elaborator_beside_a_run_time_reader_needs_a_reason(self):
        # the text cannot tell `destr` from an elaborator that calls the imported `check`: the
        # module is a candidate until NOT_READERS says its syntax reads nothing; only then are
        # its importers left alone
        files = {"T.Lib": READ, "T.Pure": 'import T.Lib\nelab "destr" : tactic => pure ()\n',
                 "T.Use": "import T.Pure\nexample : True := by destr\n"}
        self.assertEqual(self.flagged(files), {"T.Pure", "T.Use"})
        self.assertEqual(self.flagged(files, not_readers={"T.Pure"}), {"T.Pure"})
        # no reading call anywhere among its imports: no candidate
        self.assertEqual(self.flagged({"T.Pure": 'elab "destr" : tactic => pure ()\n',
                                       "T.Use": "import T.Pure\nexample : True := by destr\n"}), set())

    def test_no_candidate(self):
        files = {"T.Main": READ + "def main : IO Unit := check\n",           # reads when it runs
                 "T.Doc": READ + "-- #eval check\n/- run_cmd check\n#eval check -/\n",  # only in comments
                 "T.Text": "/-- docs: IO.FS.readFile -/\ndef x := 1\n#eval x\n",  # the read is a comment
                 "T.Guard": READ + "#guard 1 + 1 == 2\nexample : evaluate = 1 := rfl\n"}
        self.assertEqual(self.flagged(files), set())


class ReadersOf(unittest.TestCase):
    TABLE = {"T.File": ["fix/a.trace"], "T.Dir": ["corpus/clif/", "fix/list.trace"], "T.Pin": ["scripts/pin.sh"]}

    def test_files_and_directories(self):
        of = lambda *files: ei.readers_of(files, self.TABLE)
        self.assertEqual(of("fix/a.trace"), {"T.File"})
        self.assertEqual(of("corpus/clif/x.clif", "corpus/clif/sub/y.clif"), {"T.Dir"})
        self.assertEqual(of("fix/list.trace", "scripts/pin.sh", "docs/x.md"), {"T.Dir", "T.Pin"})
        # no prefix matches without the `/`, no match below a file
        self.assertEqual(of("corpus/clif2/x.clif", "corpus/clif", "fix/a.trace.bak", "fix/a.trace/x", "fix/b.trace"), set())
        self.assertEqual(of(), set())


class Table(unittest.TestCase):
    """The real tree."""

    @classmethod
    def setUpClass(cls):
        _, cls.mods, cls.imports = ei.load_lsb().load_modules(ROOT)
        cls.found = ei.candidates(cls.mods, cls.imports, ei.NOT_READERS)

    def test_every_candidate_has_a_row(self):
        # A module that may read a file while it elaborates needs a row in READERS of
        # scripts/elab-inputs.py (the files it reads: the gate then elaborates it again on every
        # run, #1012), or in NOT_READERS with the reason it reads nothing.
        self.assertEqual(sorted(self.found - ei.READERS.keys() - ei.NOT_READERS.keys()), [])

    def test_no_stale_row(self):
        self.assertEqual(sorted(ei.READERS.keys() - self.found), [], "a READERS module is no candidate any more")
        self.assertEqual(sorted(ei.NOT_READERS.keys() - self.found), [], "a NOT_READERS module is no candidate")
        self.assertEqual(sorted(ei.READERS.keys() & ei.NOT_READERS.keys()), [])
        self.assertTrue(all(isinstance(why, str) and why for why in ei.NOT_READERS.values()))

    def test_inputs_exist(self):
        for m, inputs in ei.READERS.items():
            self.assertTrue(inputs, m)
            for i in inputs:
                p = ROOT / i
                self.assertTrue(p.is_dir() if i.endswith("/") else p.is_file(), f"{m}: {i}")

    def test_paths_in_the_readers_sources_are_inputs(self):
        # every path literal a reader's source passes to a reading call is one of its inputs
        pin = "scripts/fetch-third-party.sh"
        for m, inputs in ei.READERS.items():
            text = ei.code(self.mods[m].read_text())
            literals = re.findall(r'(?:readFile|readBinFile|lines)\s+s?!?"([^"{]*)', text)
            self.assertTrue(literals or m == "FVTest.Isle.OptCorpus", m)
            for path in literals:
                wanted = pin if path.startswith("third_party/wasmtime/") else path
                self.assertIn(wanted, inputs, f"{m} reads {path}")

    def test_files_named_by_the_corpus_trace_are_inputs(self):
        # FVTest.Isle.OptCorpus reads the files its trace names
        trace = (ROOT / "FVTest/Isle/oracle/opt_corpus.trace").read_text()
        named = re.findall(r"^file (\S+)", trace, re.M)
        self.assertGreater(len(named), 10)
        self.assertEqual(ei.readers_of(named) - {"FVTest.Isle.OptCorpus"}, set())
        for f in named:
            self.assertEqual(ei.readers_of([f]), {"FVTest.Isle.OptCorpus"}, f)

    def test_the_wasmtime_pin_is_where_the_table_says(self):
        self.assertIn("WASMTIME_COMMIT=", (ROOT / "scripts/fetch-third-party.sh").read_text())


class Check(unittest.TestCase):
    def run_check(self, failing=(), fetch_rc=0, error_text=(), git=(0, "")):
        calls = []

        def run(cmd, **kw):
            calls.append((cmd, kw))
            if cmd[0].endswith("fetch-third-party.sh"):
                return types.SimpleNamespace(returncode=fetch_rc, stdout="pin mismatch\n" if fetch_rc else "")
            if cmd[0] == "git":
                return types.SimpleNamespace(returncode=git[0], stdout=git[1])
            source = cmd[-1]
            if source in failing:
                return types.SimpleNamespace(returncode=1, stdout=f"{source}:66:0: error: oracle mismatch\n")
            if source in error_text:
                return types.SimpleNamespace(returncode=0, stdout=f"{source}:66:0: error: oracle mismatch\n")
            return types.SimpleNamespace(returncode=0, stdout="")

        out = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(out):
            status = ei.check(pathlib.Path(tmp) / "logs", run=run)
            logs = sorted(p.name for p in (pathlib.Path(tmp) / "logs").glob("*.log"))
        return status, out.getvalue(), calls, logs

    def test_every_reader_is_elaborated_from_its_source(self):
        status, out, calls, logs = self.run_check()
        self.assertEqual(status, 0)
        self.assertEqual(calls[0][0][1:], ["wasmtime"])
        self.assertEqual(calls[1][0], ["git", "-C", str(ROOT / "third_party/wasmtime"), "status", "--porcelain",
                                       "--untracked-files=no", "--", "cranelift/codegen"])
        sources = [cmd[-1] for cmd, _ in calls[2:]]
        self.assertEqual(sorted(sources), sorted(m.replace(".", "/") + ".lean" for m in ei.READERS))
        for cmd, kw in calls[2:]:
            self.assertEqual(cmd[:2], ["lake", "lean"])             # the source itself, not `lake build`
            self.assertEqual(pathlib.Path(kw["cwd"]), ROOT)         # the readers' paths are relative to the root
        n = len(ei.READERS)
        self.assertIn(f"elaboration-time inputs: {n} of {n} reading modules re-elaborated", out.splitlines()[-1])
        self.assertEqual(logs, sorted(f"{m}.log" for m in ei.READERS))

    def test_a_failing_reader_fails_the_line(self):
        for kind in ("failing", "error_text"):
            status, out, calls, _ = self.run_check(**{kind: ["FVTest/Isle/Interp.lean"]})
            self.assertEqual(status, 1, kind)
            self.assertIn("FAIL FVTest.Isle.Interp", out)
            self.assertIn("oracle mismatch", out)
            self.assertIn("FAILED FVTest.Isle.Interp", out.splitlines()[-1])
            self.assertEqual(len(calls), 2 + len(ei.READERS))     # the others still run

    def test_a_wrong_pin_fails_before_anything_is_elaborated(self):
        status, out, calls, _ = self.run_check(fetch_rc=1)
        self.assertEqual(status, 1)
        self.assertEqual(len(calls), 1)
        self.assertIn("fetch-third-party.sh wasmtime failed", out)

    def test_edited_wasmtime_sources_fail_before_anything_is_elaborated(self):
        # review finding (CiGate4Review2 1): the fetch script compares the commit only; a kept
        # checkout with an edited ISLE source at the pinned commit passed
        for git, text in (((0, " M cranelift/codegen/src/isa/aarch64/inst.isle\n"), "1 file(s) differ"),
                          ((128, "fatal: not a git repository\n"), "git status failed")):
            status, out, calls, _ = self.run_check(git=git)
            self.assertEqual(status, 1)
            self.assertEqual(len(calls), 2)
            self.assertIn("third_party/wasmtime/cranelift/codegen is not the pinned commit's", out)
            self.assertIn(text, out)


class ModifiedSources(unittest.TestCase):
    def test_tracked_changes_below_the_directory_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = pathlib.Path(tmp)

            def git(*a):
                r = subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false", *a],
                                   cwd=repo, capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stderr)

            for f in ("cranelift/codegen/src/a.isle", "cranelift/filetests/src/b.rs"):
                (repo / f).parent.mkdir(parents=True)
                (repo / f).write_text("x\n")
            git("init", "-q"); git("add", "-A"); git("commit", "-q", "-m", "pin")
            self.assertEqual(ei.modified_sources(repo, "cranelift/codegen"), [])
            # the stock comparison's patch touches cranelift/filetests only; new files are not read
            (repo / "cranelift/filetests/src/b.rs").write_text("patched\n")
            (repo / "cranelift/codegen/src/new.isle").write_text("untracked\n")
            self.assertEqual(ei.modified_sources(repo, "cranelift/codegen"), [])
            (repo / "cranelift/codegen/src/a.isle").write_text("edited\n")
            self.assertEqual(ei.modified_sources(repo, "cranelift/codegen"), [" M cranelift/codegen/src/a.isle"])
            git("add", "cranelift/codegen/src/a.isle")               # staged, working tree equal to the index
            self.assertEqual(ei.modified_sources(repo, "cranelift/codegen"), ["M  cranelift/codegen/src/a.isle"])
            git("commit", "-q", "-m", "moved")                       # HEAD moved: the fetch script's part
            self.assertEqual(ei.modified_sources(repo, "cranelift/codegen"), [])
            (repo / "cranelift/codegen/src/a.isle").unlink()
            self.assertEqual(ei.modified_sources(repo, "cranelift/codegen"), [" D cranelift/codegen/src/a.isle"])
            self.assertIsNone(ei.modified_sources(repo / "missing", "cranelift/codegen"))


class GateLines(unittest.TestCase):
    def test_the_full_gate_and_the_local_gate_run_the_check(self):
        workflow = (ROOT / ".github/workflows/full-gate.yml").read_text()
        audit = workflow.split("\n  audit:\n")[1].split("\n  crate-proofs:\n")[0]
        self.assertIn("scripts/elab-inputs.py check", audit)
        self.assertIn("scripts/elab-inputs.py check", (ROOT / "scripts/main-gate.sh").read_text())


if __name__ == "__main__":
    unittest.main()
