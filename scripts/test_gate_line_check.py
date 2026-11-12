import importlib.util, pathlib, subprocess, sys, tempfile, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("gate_line_check", HERE / "gate-line-check.py")
gc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gc)

FUNCS = ("cargo fv: 3251 of 3251 functions compiled by the Lean backend (3251 verified): your crate(s) 3251 of 3251 "
         "(3251 verified), dependencies 0 of 0 (0 verified); report: /w/target/fv-report.json\n")
SAME = FUNCS + "SAME: 16 test outcomes identical (logs: /tmp/fv-compare.v7WPxm)\n"
OUT = "/w/examples/survey/target/fv/plain-leanlink-verified-leanld/aarch64-unknown-linux-musl/debug/build"
FORMS = "stp (q) [xn], #simm\t100\t83\t0\nstlxr\t100\t74\t0\n"
KNOWN = [("b_slices/values", "#1003"), ("e_option_result/values", "#1003")]
LIST = ("# comment\n\nsurvey  b_slices/values  #1003\nsurvey  e_option_result/values  #1003\n"
        "other  pkg/exe  #7\n")
# cargo fv's own log of a healthy --lean-link run, and the lines of the two fallbacks the CI gate
# ran on until #1001 (lean-ld and link-check were not restored)
LEAN_LD = ("   Compiling a_arith v0.1.0 (/w/examples/survey/a_arith)\n"
           f"         fv-rustc: {OUT}/a_arith/e3ea9c8990bd8ccd/out/a_arith-e3ea9c8990bd8ccd: linked by lean-ld in 412 ms\n"
           "test tests::missing_key_is_none ... ok\n")
NO_LEAN_LD = ("warning: linker stderr: fv-rustc: --lean-ld: cannot run /w/.lake/build/bin/lean-ld (lake build lean-ld): "
              "No such file or directory (os error 2); linking with rust-lld\n"
              f"         fv-rustc: {OUT}/a_arith/e3ea9c8990bd8ccd/out/a_arith-e3ea9c8990bd8ccd: linked by rust-lld in 51 ms\n")
NO_LINK_CHECK = "cargo fv link-proof: /w/.lake/build/bin/link-check missing (lake build link-check); run it on /w/bin-check/x\n"


def fv(log, binary_check, known=(), fv_log=LEAN_LD):
    return gc.cargo_fv(log, binary_check, known, fv_log)


def exe(package, stem, verdict="verified: E2E.Binary.binary_correct holds for its 70 Lean-compiled functions",
        h="e3ea9c8990bd8ccd"):
    return f"cargo fv: binary {OUT}/{package}/{h}/out/{stem}-{h}: {verdict}\n"


def count(n, m):
    return f'cargo fv: binary check: {n} of {m} executable(s) verified (docs/contracts/e2e.md, "Binary level (M9)")\n'


def survey(bad=("b_slices", "e_option_result"), reason="not verified: 3 of 365 Lean-compiled functions fail (first: f: returnPins)"):
    """A survey log: a unit-test and a `values` executable per crate; `values` of `bad` unverified."""
    crates = ["a_arith", "b_slices", "c_structs_enums", "e_option_result"]
    body = "".join(exe(c, c) + (exe(c, "values", reason) if c in bad else exe(c, "values")) for c in crates)
    return body + count(2 * len(crates) - len(bad), 2 * len(crates)) + SAME


def total(forms, vectors, faults, failures):
    return f"TOTAL forms {forms} vectors {vectors} faults {faults} failures {failures}\n"


GREEN = exe("a", "a") + count(1, 1) + SAME


class CargoFv(unittest.TestCase):
    def test_green(self):
        # the local gate's deps line on 9ae930c5
        log = "".join(exe("deps-demo", s) for s in ("crates", "deps_demo", "deps_demo", "deps_demo")) + count(4, 4) + SAME
        ok, line = fv(log, True)
        self.assertTrue(ok, line)
        self.assertIn("binary check: 4 of 4", line)
        self.assertIn("SAME: 16", line)
        self.assertNotIn("FAIL", line)

    def test_link_check_missing(self):
        # #998: the CI jobs never restored link-check; every executable "not checked", job green
        not_checked = "not checked: cargo fv link-proof: /w/.lake/build/bin/link-check missing (lake build link-check)"
        log = exe("a_arith", "a_arith", not_checked) + exe("a_arith", "values", not_checked) + count(0, 2) + SAME
        ok, line = fv(log, True)
        self.assertFalse(ok)
        self.assertIn("FAIL: not verified: a_arith/a_arith", line)
        self.assertIn("FAIL: not verified: a_arith/values", line)

    def test_some_executables_unverified(self):
        ok, line = fv(survey(), True)
        self.assertFalse(ok)
        self.assertIn("FAIL: not verified: b_slices/values", line)
        self.assertIn("FAIL: not verified: e_option_result/values", line)

    def test_no_executable_checked(self):
        # cargo fv prints no count when no executable has Lean-compiled code
        ok, line = fv(SAME, True)
        self.assertFalse(ok)
        self.assertIn("0 `binary check:` lines", line)
        self.assertFalse(fv(count(0, 0) + SAME, True)[0])

    def test_count_line(self):
        self.assertFalse(fv(exe("a", "a") + count(1, 1) + count(1, 1) + SAME, True)[0])
        self.assertFalse(fv("cargo fv: binary check: all executable(s) verified\n" + SAME, True)[0])
        # the count must be the per-executable lines' (an executable line lost, a wrong count)
        self.assertFalse(fv(exe("a", "a") + count(2, 2) + SAME, True)[0])
        self.assertFalse(fv(exe("a", "a") + exe("a", "values", "not verified: x") + count(2, 2) + SAME, True)[0])
        self.assertFalse(fv(count(4, 4) + SAME, True)[0])

    def test_without_binary_check(self):
        # examples/bigframe-unwind (plain `cargo fv`, rust-lld): its one executable is outside the
        # binary check
        log = exe("bigframe-unwind", "bigframe_unwind", "not verified: link-check ran no binary check (lake build link-check)")
        log += count(0, 1) + FUNCS + "SAME: 2 test outcomes identical (logs: /t)\n"
        self.assertTrue(fv(log, False, fv_log=log)[0])
        self.assertTrue(fv(SAME, False, fv_log="")[0])

    def test_same_line(self):
        for flag in (False, True):
            self.assertTrue(fv(GREEN, flag)[0])
            self.assertFalse(fv(exe("a", "a") + count(1, 1) + FUNCS, flag)[0])
            self.assertFalse(fv(exe("a", "a") + count(1, 1) + FUNCS + "DIFFERENT or failing (logs: /t)\n", flag)[0])
            self.assertFalse(fv(GREEN + "DIFFERENT or failing (logs: /t)\n", flag)[0])
            # no test ran on either side: nothing was compared
            self.assertFalse(fv(exe("a", "a") + count(1, 1) + FUNCS + "SAME: 0 test outcomes identical (logs: /t)\n", flag)[0])
            # only at the start of a line
            self.assertFalse(fv(exe("a", "a") + count(1, 1) + FUNCS + "  note: SAME: 3 test outcomes identical\n", flag)[0])
            # review finding (PR #1001, round 2): two valid SAME lines (two logs concatenated) passed
            ok, line = fv(GREEN + "SAME: 16 test outcomes identical (logs: /t)\n", flag)
            self.assertFalse(ok)
            self.assertIn("FAIL: 2 SAME lines, want 1", line)

    def test_lean_compiled_functions(self):
        # SAME says nothing about the Lean backend when every function kept cg_clif's code
        same = "SAME: 16 test outcomes identical (logs: /t)\n"
        zero = "cargo fv: 0 of 1378 functions compiled by the Lean backend (0 verified): your crate(s) 0 of 1378 (0 verified)\n"
        for flag in (False, True):
            ok, line = fv(exe("a", "a") + count(1, 1) + zero + same, flag)
            self.assertFalse(ok)
            self.assertIn("FAIL: no function compiled by the Lean backend", line)
            self.assertFalse(fv(exe("a", "a") + count(1, 1) + same, flag)[0])
            self.assertFalse(fv(exe("a", "a") + count(1, 1) + FUNCS + FUNCS + same, flag)[0])
        # the counts are part of the verdict line (the report on #261 shows them on every run)
        self.assertIn("3251 of 3251 functions compiled by the Lean backend (3251 verified)", fv(GREEN, True)[1])

    def test_exe_name(self):
        self.assertEqual(gc.exe_name(f"{OUT}/b_slices/c2219a14186b9eba/out/values-c2219a14186b9eba"), "b_slices/values")
        self.assertEqual(gc.exe_name(f"{OUT}/deps-demo/3788048fba79df40/out/deps_demo"), "deps-demo/deps_demo")
        self.assertEqual(gc.exe_name(f"{OUT}/fv-demo/aa3f2cd4890b3234/out/fv_demo-aa3f2cd4890b3234"), "fv-demo/fv_demo")
        # an unexpected path keeps its full name: it can match no list entry
        self.assertEqual(gc.exe_name("/w/out/values"), "/w/out/values")


class Fallbacks(unittest.TestCase):
    """cargo fv's own log: a missing tool or a fallback is red (#1004)."""

    def test_rust_lld_instead_of_lean_ld(self):
        # the CI gate before #1001: lean-ld not restored, every link by rust-lld, tests SAME
        ok, line = fv(GREEN, True, fv_log=NO_LEAN_LD)
        self.assertFalse(ok)
        self.assertIn("FAIL: fallback or missing tool: warning: linker stderr: fv-rustc: --lean-ld: cannot run", line)
        self.assertIn("FAIL: 1 link(s) by rust-lld, want lean-ld", line)
        self.assertIn("FAIL: no `linked by lean-ld` line", line)

    def test_lean_ld_rejects_an_input(self):
        rejected = (LEAN_LD + "warning: linker stderr: fv-rustc: --lean-ld: /w/.lake/build/bin/lean-ld failed, "
                    "linking with rust-lld: unsupported relocation\n         fv-rustc: /w/x: linked by rust-lld in 9 ms\n")
        self.assertFalse(fv(GREEN, True, fv_log=rejected)[0])

    def test_one_link_by_rust_lld_among_lean_ld(self):
        self.assertFalse(fv(GREEN, True, fv_log=LEAN_LD + "         fv-rustc: /w/y: linked by rust-lld in 9 ms\n")[0])

    def test_lean_ld_line_required_only_with_lean_link(self):
        self.assertFalse(fv(GREEN, True, fv_log="")[0])
        self.assertTrue(fv(GREEN, False, fv_log="")[0])

    def test_link_check_missing_line(self):
        # red on every line, also where no binary check is asked (plain cargo fv)
        for flag in (False, True):
            ok, line = fv(GREEN, flag, fv_log=LEAN_LD + NO_LINK_CHECK)
            self.assertFalse(ok)
            self.assertIn("link-check missing", line)

    def test_not_checked_line(self):
        self.assertFalse(fv(GREEN, False, fv_log="cargo fv: binary /w/x: not checked: cargo-fv's path is unknown\n")[0])

    def test_only_cargo_fv_lines(self):
        # a test or a crate may say "missing"; only cargo fv's and fv-rustc's lines count
        noise = ("test tests::missing_key_is_none ... ok\nwarning: missing documentation for a function\n"
                 "thread 'main' panicked: cannot run without an argument\n")
        self.assertTrue(fv(GREEN, True, fv_log=LEAN_LD + noise)[0])

    def test_repeated_line_reported_once(self):
        ok, line = fv(GREEN, False, fv_log=NO_LINK_CHECK * 5)
        self.assertEqual(line.count("link-check missing"), 1)


class KnownUnverified(unittest.TestCase):
    """The exact list (#1003): green iff the unverified executables are exactly the listed ones."""

    def test_exactly_the_list(self):
        ok, line = fv(survey(), True, KNOWN)
        self.assertTrue(ok, line)
        self.assertIn("binary check: 6 of 8", line)
        self.assertIn("known unverified (scripts/gate-known-unverified.txt): b_slices/values #1003, e_option_result/values #1003", line)

    def test_one_more_unverified(self):
        ok, line = fv(survey(bad=("a_arith", "b_slices", "e_option_result")), True, KNOWN)
        self.assertFalse(ok)
        self.assertIn("FAIL: not verified: a_arith/values", line)
        self.assertNotIn("FAIL: not verified: b_slices", line)

    def test_fixed_entry_must_be_removed(self):
        ok, line = fv(survey(bad=("b_slices",)), True, KNOWN)
        self.assertFalse(ok)
        self.assertIn("e_option_result/values is in the known-unverified list (#1003) but is verified or absent: remove the entry", line)
        ok, line = fv(survey(bad=()), True, KNOWN)
        self.assertFalse(ok)
        self.assertEqual(line.count("remove the entry"), 2)

    def test_listed_executable_absent(self):
        log = exe("a_arith", "a_arith") + count(1, 1) + SAME
        self.assertFalse(fv(log, True, KNOWN)[0])

    def test_same_name_is_not_same_executable(self):
        # the list names b_slices' `values`; a_arith's `values` failing instead is not that
        ok, line = fv(survey(bad=("a_arith", "e_option_result")), True, KNOWN)
        self.assertFalse(ok)
        self.assertIn("FAIL: not verified: a_arith/values", line)
        self.assertIn("b_slices/values is in the known-unverified list", line)

    def test_every_executable_not_checked(self):
        # link-check missing: the two listed executables match, the other six do not
        log = survey(bad=("a_arith", "b_slices", "c_structs_enums", "e_option_result"), reason="not checked: link-check missing")
        self.assertFalse(fv(log, True, KNOWN)[0])

    def test_two_executables_of_one_name(self):
        log = exe("fv-demo", "fv_demo", "not verified: x", "aa3f2cd4890b3234") + exe("fv-demo", "fv_demo", "not verified: x", "b5195c07001282a7")
        log += count(0, 2) + SAME
        one = [("fv-demo/fv_demo", "#9")]
        self.assertFalse(fv(log, True, one)[0])
        self.assertTrue(fv(log, True, one + one)[0])

    def test_list_only_with_binary_check(self):
        self.assertTrue(fv(survey(bad=()), False, KNOWN)[0])

    def test_read_known(self):
        self.assertEqual(gc.read_known(LIST, "survey"), (KNOWN, []))
        self.assertEqual(gc.read_known(LIST, "fv-demo"), ([], []))
        self.assertEqual(gc.read_known(LIST, "other"), ([("pkg/exe", "#7")], []))
        for bad in ("survey b_slices/values\n", "survey values #1003\n", "survey b_slices/values 1003\n",
                    "survey b_slices/values #1003 extra\n"):
            self.assertEqual(len(gc.read_known(bad, "fv-demo")[1]), 1, bad)

    def test_checked_in_list(self):
        # the list in the repository parses, and every entry has an issue
        text = (HERE / "gate-known-unverified.txt").read_text()
        examples = {l.split()[0] for l in text.splitlines() if l.strip() and not l.lstrip().startswith("#")}
        for e in examples | {"fv-demo", "deps"}:
            self.assertEqual(gc.read_known(text, e)[1], [])
        # fv-demo and deps stay strict
        self.assertEqual(gc.read_known(text, "fv-demo")[0], [])
        self.assertEqual(gc.read_known(text, "deps")[0], [])


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
        return subprocess.run([sys.executable, str(HERE / "gate-line-check.py"), *map(str, a)], capture_output=True, text=True)

    def test_cargo_fv(self):
        with tempfile.TemporaryDirectory() as t:
            t = pathlib.Path(t)
            log, known, fvlog = t / "survey.log", t / "known.txt", t / "fv.log"
            log.write_text(survey())
            known.write_text(LIST)
            fvlog.write_text(LEAN_LD)
            self.assertEqual(self.run_script("cargo-fv", log, fvlog).returncode, 0)
            r = self.run_script("cargo-fv", "--binary-check", "survey", "--known", known, log, fvlog)
            self.assertEqual((r.returncode, len(r.stdout.splitlines())), (0, 1), r.stdout)
            # the list is per example: the same log under another example's name is red
            r = self.run_script("cargo-fv", "--binary-check", "fv-demo", "--known", known, log, fvlog)
            self.assertEqual(r.returncode, 1)
            self.assertIn("FAIL: not verified: b_slices/values", r.stdout)
            # cargo fv's own log decides too
            fvlog.write_text(NO_LEAN_LD)
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "survey", "--known", known, log, fvlog).returncode, 1)
            fvlog.write_text(LEAN_LD)
            # an unreadable list line is red for every example
            known.write_text(LIST + "survey oops\n")
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "survey", "--known", known, log, fvlog).returncode, 1)
            # a missing log or list is a failure, not a pass
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "survey", str(log) + ".absent", fvlog).returncode, 1)
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "survey", log, str(fvlog) + ".absent").returncode, 1)
            self.assertEqual(self.run_script("cargo-fv", log, "/fv.log").returncode, 1)
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "survey", "--known", str(known) + ".absent", log, fvlog).returncode, 1)

    def test_default_list(self):
        # without --known the checked-in list applies
        with tempfile.TemporaryDirectory() as t:
            log, fvlog = pathlib.Path(t) / "deps.log", pathlib.Path(t) / "fv.log"
            fvlog.write_text(LEAN_LD)
            log.write_text(exe("deps-demo", "deps_demo") + count(1, 1) + SAME)
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "deps", log, fvlog).returncode, 0)
            log.write_text(exe("deps-demo", "deps_demo", "not verified: x") + count(0, 1) + SAME)
            self.assertEqual(self.run_script("cargo-fv", "--binary-check", "deps", log, fvlog).returncode, 1)

    def test_arm_fault_cosim(self):
        with tempfile.TemporaryDirectory() as t:
            log = pathlib.Path(t) / "faultcosim.log"
            log.write_text(FORMS + total(152, 15200, 10318, 0))
            self.assertEqual(self.run_script("arm-fault-cosim", log).returncode, 0)
            log.write_text(FORMS + total(152, 15200, 0, 0))
            self.assertEqual(self.run_script("arm-fault-cosim", log).returncode, 1)
            self.assertEqual(self.run_script("arm-fault-cosim", str(log) + ".absent").returncode, 1)

    def test_usage(self):
        # a wrong call is an error (status 2), never a verdict
        for a in ([], ["cargo-fv"], ["cargo-fv", "a.log"], ["cargo-fv", "--binary-check"],
                  ["cargo-fv", "--binary-check", "a.log", "fv.log"], ["deps.log"], ["float-spec", "x.log"],
                  ["arm-fault-cosim", "--binary-check", "survey", "x.log"], ["arm-fault-cosim", "a.log", "b.log"],
                  ["cargo-fv", "a.log", "b.log", "c.log"], ["cargo-fv", "--known", "k.txt", "a.log", "fv.log"],
                  ["cargo-fv", "--binary-check", "survey", "--binary-check", "deps", "a.log", "fv.log"],
                  ["cargo-fv", "--binary-check", "", "a.log", "fv.log"], ["cargo-fv", "--verified", "a.log", "fv.log"]):
            self.assertEqual(self.run_script(*a).returncode, 2, a)


if __name__ == "__main__":
    unittest.main()
