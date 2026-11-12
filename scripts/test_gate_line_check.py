import importlib.util, pathlib, subprocess, sys, tempfile, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("gate_line_check", HERE / "gate-line-check.py")
gc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gc)

SAME = "SAME: 16 test outcomes identical (logs: /tmp/fv-compare.v7WPxm)\n"
EXE = "cargo fv: binary /w/out/a_arith-e3ea9c8990bd8ccd: "
FORMS = "stp (q) [xn], #simm\t100\t83\t0\nstlxr\t100\t74\t0\n"


def binary(n, m):
    return f'cargo fv: binary check: {n} of {m} executable(s) verified (docs/contracts/e2e.md, "Binary level (M9)")\n'


def total(forms, vectors, faults, failures):
    return f"TOTAL forms {forms} vectors {vectors} faults {faults} failures {failures}\n"


class CargoFv(unittest.TestCase):
    def test_green(self):
        # the local gate's deps line on 9ae930c5
        ok, line = gc.cargo_fv(EXE + "verified: E2E.Binary.binary_correct holds\n" + binary(4, 4) + SAME, True)
        self.assertTrue(ok)
        self.assertIn("binary check: 4 of 4", line)
        self.assertIn("SAME: 16", line)
        self.assertNotIn("FAIL", line)

    def test_link_check_missing(self):
        # #998: the CI jobs never restored link-check; every executable "not checked", job green
        log = EXE + "not checked: cargo fv link-proof: /w/.lake/build/bin/link-check missing\n" + binary(0, 18) + SAME
        ok, line = gc.cargo_fv(log, True)
        self.assertFalse(ok)
        self.assertIn("FAIL: binary check: 0 of 18", line)

    def test_some_executables_unverified(self):
        self.assertFalse(gc.cargo_fv(binary(17, 18) + SAME, True)[0])

    def test_no_executable_checked(self):
        # cargo fv prints no count when no executable has Lean-compiled code
        ok, line = gc.cargo_fv(SAME, True)
        self.assertFalse(ok)
        self.assertIn("no `binary check:` line", line)
        self.assertFalse(gc.cargo_fv(binary(0, 0) + SAME, True)[0])

    def test_every_count_line_must_hold(self):
        self.assertFalse(gc.cargo_fv(binary(2, 2) + binary(0, 1) + SAME, True)[0])
        self.assertFalse(gc.cargo_fv("cargo fv: binary check: all executable(s) verified\n" + SAME, True)[0])

    def test_without_binary_check(self):
        # examples/bigframe-unwind (plain `cargo fv`): its one executable is outside the binary check
        self.assertTrue(gc.cargo_fv(binary(0, 1) + "SAME: 2 test outcomes identical (logs: /t)\n", False)[0])
        self.assertTrue(gc.cargo_fv(SAME, False)[0])

    def test_same_line(self):
        for flag in (False, True):
            self.assertFalse(gc.cargo_fv(binary(4, 4), flag)[0])
            self.assertFalse(gc.cargo_fv(binary(4, 4) + "DIFFERENT or failing (logs: /t)\n", flag)[0])
            self.assertFalse(gc.cargo_fv(binary(4, 4) + SAME + "DIFFERENT or failing (logs: /t)\n", flag)[0])
            # no test ran on either side: nothing was compared
            self.assertFalse(gc.cargo_fv(binary(4, 4) + "SAME: 0 test outcomes identical (logs: /t)\n", flag)[0])
            # only at the start of a line
            self.assertFalse(gc.cargo_fv(binary(4, 4) + "  note: SAME: 3 test outcomes identical\n", flag)[0])


class ArmFaultCosim(unittest.TestCase):
    def test_green(self):
        # the local gate's line on 9ae930c5
        ok, line = gc.arm_fault_cosim(FORMS + total(152, 15200, 10318, 0))
        self.assertTrue(ok)
        self.assertEqual(line, "TOTAL forms 152 vectors 15200 faults 10318 failures 0")

    def test_failures(self):
        ok, line = gc.arm_fault_cosim(FORMS + "FAIL stlxr inst 0x0: [x]\n" + total(152, 15200, 10318, 2))
        self.assertFalse(ok)
        self.assertIn("FAIL: 2 failures", line)

    def test_nothing_exercised(self):
        # review finding (PR #1001): `faults 0` with vectors and no failure was accepted, although
        # no vector reached the memory-fault behaviour the gate is about
        self.assertFalse(gc.arm_fault_cosim(total(152, 15200, 0, 0))[0])
        self.assertTrue(gc.arm_fault_cosim(total(152, 15200, 1, 0))[0])
        self.assertFalse(gc.arm_fault_cosim(total(0, 0, 0, 0))[0])
        self.assertFalse(gc.arm_fault_cosim(total(152, 0, 0, 0))[0])

    def test_total_line(self):
        self.assertFalse(gc.arm_fault_cosim(FORMS)[0])
        self.assertFalse(gc.arm_fault_cosim("")[0])
        self.assertFalse(gc.arm_fault_cosim("TOTAL forms 152 vectors many faults 3 failures 0\n")[0])
        self.assertFalse(gc.arm_fault_cosim(total(152, 15200, 10318, 0) + total(152, 15200, 10318, 0))[0])
        self.assertFalse(gc.arm_fault_cosim("note TOTAL forms 152 vectors 15200 faults 10318 failures 0\n")[0])


class CommandLine(unittest.TestCase):
    def run_script(self, *a):
        return subprocess.run([sys.executable, str(HERE / "gate-line-check.py"), *a], capture_output=True, text=True)

    def test_cargo_fv(self):
        with tempfile.TemporaryDirectory() as t:
            log = pathlib.Path(t) / "deps.log"
            log.write_text(binary(0, 4) + SAME)
            self.assertEqual(self.run_script("cargo-fv", str(log)).returncode, 0)
            r = self.run_script("cargo-fv", "--binary-check", str(log))
            self.assertEqual(r.returncode, 1)
            self.assertIn("FAIL: binary check: 0 of 4", r.stdout)
            self.assertEqual(len(r.stdout.splitlines()), 1)
            # a missing log is a failure, not a pass
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", str(log) + ".absent").returncode, 1)

    def test_arm_fault_cosim(self):
        with tempfile.TemporaryDirectory() as t:
            log = pathlib.Path(t) / "faultcosim.log"
            log.write_text(FORMS + total(152, 15200, 10318, 0))
            self.assertEqual(self.run_script("arm-fault-cosim", str(log)).returncode, 0)
            log.write_text(FORMS + total(152, 15200, 0, 0))
            self.assertEqual(self.run_script("arm-fault-cosim", str(log)).returncode, 1)
            self.assertEqual(self.run_script("arm-fault-cosim", str(log) + ".absent").returncode, 1)

    def test_usage(self):
        # a wrong call is an error (status 2), never a verdict
        for a in ([], ["cargo-fv"], ["cargo-fv", "--binary-check"], ["deps.log"], ["float-spec", "x.log"],
                  ["arm-fault-cosim", "--binary-check", "x.log"], ["cargo-fv", "a.log", "b.log"]):
            self.assertEqual(self.run_script(*a).returncode, 2, a)


if __name__ == "__main__":
    unittest.main()
