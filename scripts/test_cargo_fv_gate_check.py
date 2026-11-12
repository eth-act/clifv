import importlib.util, pathlib, subprocess, sys, tempfile, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("cargo_fv_gate_check", HERE / "cargo-fv-gate-check.py")
gc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gc)

SAME = "SAME: 16 test outcomes identical (logs: /tmp/fv-compare.v7WPxm)\n"
EXE = "cargo fv: binary /w/out/a_arith-e3ea9c8990bd8ccd: "


def binary(n, m):
    return f'cargo fv: binary check: {n} of {m} executable(s) verified (docs/contracts/e2e.md, "Binary level (M9)")\n'


class CargoFvGateCheck(unittest.TestCase):
    def test_green(self):
        # the local gate's deps line on 9ae930c5
        ok, line = gc.verdict(EXE + "verified: E2E.Binary.binary_correct holds\n" + binary(4, 4) + SAME, True)
        self.assertTrue(ok)
        self.assertIn("binary check: 4 of 4", line)
        self.assertIn("SAME: 16", line)
        self.assertNotIn("FAIL", line)

    def test_link_check_missing(self):
        # #998: the CI jobs never restored link-check; every executable "not checked", job green
        log = EXE + "not checked: cargo fv link-proof: /w/.lake/build/bin/link-check missing\n" + binary(0, 18) + SAME
        ok, line = gc.verdict(log, True)
        self.assertFalse(ok)
        self.assertIn("FAIL: binary check: 0 of 18", line)

    def test_some_executables_unverified(self):
        self.assertFalse(gc.verdict(binary(17, 18) + SAME, True)[0])

    def test_no_executable_checked(self):
        # cargo fv prints no count when no executable has Lean-compiled code
        ok, line = gc.verdict(SAME, True)
        self.assertFalse(ok)
        self.assertIn("no `binary check:` line", line)
        self.assertFalse(gc.verdict(binary(0, 0) + SAME, True)[0])

    def test_every_count_line_must_hold(self):
        self.assertFalse(gc.verdict(binary(2, 2) + binary(0, 1) + SAME, True)[0])
        self.assertFalse(gc.verdict("cargo fv: binary check: all executable(s) verified\n" + SAME, True)[0])

    def test_without_binary_check(self):
        # examples/bigframe-unwind (plain `cargo fv`): its one executable is outside the binary check
        self.assertTrue(gc.verdict(binary(0, 1) + "SAME: 2 test outcomes identical (logs: /t)\n", False)[0])
        self.assertTrue(gc.verdict(SAME, False)[0])

    def test_same_line(self):
        for flag in (False, True):
            self.assertFalse(gc.verdict(binary(4, 4), flag)[0])
            self.assertFalse(gc.verdict(binary(4, 4) + "DIFFERENT or failing (logs: /t)\n", flag)[0])
            self.assertFalse(gc.verdict(binary(4, 4) + SAME + "DIFFERENT or failing (logs: /t)\n", flag)[0])
            # no test ran on either side: nothing was compared
            self.assertFalse(gc.verdict(binary(4, 4) + "SAME: 0 test outcomes identical (logs: /t)\n", flag)[0])
            # only at the start of a line
            self.assertFalse(gc.verdict(binary(4, 4) + "  note: SAME: 3 test outcomes identical\n", flag)[0])

    def test_command_line(self):
        script = str(HERE / "cargo-fv-gate-check.py")
        with tempfile.TemporaryDirectory() as t:
            log = pathlib.Path(t) / "deps.log"
            log.write_text(binary(0, 4) + SAME)
            run = lambda *a: subprocess.run([sys.executable, script, *a], capture_output=True, text=True)
            self.assertEqual(run(str(log)).returncode, 0)
            r = run("--binary-check", str(log))
            self.assertEqual(r.returncode, 1)
            self.assertIn("FAIL: binary check: 0 of 4", r.stdout)
            self.assertEqual(len(r.stdout.splitlines()), 1)
            # a missing log is a failure, not a pass; a missing argument is a usage error
            self.assertEqual(run("--binary-check", str(log) + ".absent").returncode, 1)
            self.assertEqual(run("--binary-check").returncode, 2)


if __name__ == "__main__":
    unittest.main()
