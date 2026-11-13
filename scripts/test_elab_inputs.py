import contextlib, importlib.util, io, pathlib, re, tempfile, types, unittest

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
    def flagged(self, files):
        tmp, mods, imports = tree(files)
        with tmp:
            return ei.candidates(mods, imports)

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
                        "  #eval check", "unsafe initialize check"):
            self.assertEqual(self.flagged({"T.A": READ + command + "\n"}), {"T.A"}, command)

    def test_other_readers(self):
        for call in ('IO.FS.readBinFile "x"', '(System.FilePath.mk "d").readDir', 'IO.FS.lines "x"',
                     '(System.FilePath.mk "d").walkDir', 'include_str "x"', 'IO.Process.output { cmd := "x" }',
                     'IO.Process.run { cmd := "x" }', 'h.readToEnd', 'h.getLine'):
            self.assertEqual(self.flagged({"T.A": f"def check : IO Unit := do\n  let _ ← {call}\n#eval check\n"}),
                             {"T.A"}, call)

    def test_an_elaborator_that_reads(self):
        files = {"T.Tac": READ + 'elab "load_it" : tactic => do\n  check\n',
                 # a pure elaborator in a module that imports a run-time reader is no candidate
                 "T.Pure": 'import T.Lib\nelab "destr" : tactic => pure ()\nelab_rules : tactic | `(tactic| x) => pure ()\n',
                 "T.Lib": READ}
        self.assertEqual(self.flagged(files), {"T.Tac"})

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
        cls.found = ei.candidates(cls.mods, cls.imports)

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
    def run_check(self, failing=(), fetch_rc=0, error_text=()):
        calls = []

        def run(cmd, **kw):
            calls.append((cmd, kw))
            if cmd[0].endswith("fetch-third-party.sh"):
                return types.SimpleNamespace(returncode=fetch_rc, stdout="pin mismatch\n" if fetch_rc else "")
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
        sources = [cmd[-1] for cmd, _ in calls[1:]]
        self.assertEqual(sorted(sources), sorted(m.replace(".", "/") + ".lean" for m in ei.READERS))
        for cmd, kw in calls[1:]:
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
            self.assertEqual(len(calls), 1 + len(ei.READERS))     # the others still run

    def test_a_wrong_pin_fails_before_anything_is_elaborated(self):
        status, out, calls, _ = self.run_check(fetch_rc=1)
        self.assertEqual(status, 1)
        self.assertEqual(len(calls), 1)
        self.assertIn("fetch-third-party.sh wasmtime failed", out)


class GateLines(unittest.TestCase):
    def test_the_full_gate_and_the_local_gate_run_the_check(self):
        workflow = (ROOT / ".github/workflows/full-gate.yml").read_text()
        audit = workflow.split("\n  audit:\n")[1].split("\n  crate-proofs:\n")[0]
        self.assertIn("scripts/elab-inputs.py check", audit)
        self.assertIn("scripts/elab-inputs.py check", (ROOT / "scripts/main-gate.sh").read_text())


if __name__ == "__main__":
    unittest.main()
