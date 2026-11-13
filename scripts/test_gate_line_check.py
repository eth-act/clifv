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


# the pins of the `survey()` log, and a file with them
PINNED = (8, 3251, 3251)
PINS = "# comment\n\nsurvey  8  3251  3251\nfv-demo  8  3251  3251\n"


def fv(log, lean_link, known=(), fv_log=LEAN_LD, pinned=None, example="survey"):
    """The verdict of a log; without `pinned` the log's own counts are the pins (the pins have
    their own tests, PinnedCounts)."""
    if pinned is None:
        pinned = tuple(0 if c is None else c for c in gc.measured(log.splitlines()))
    return gc.cargo_fv(example, log, lean_link, known, fv_log, pinned)


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

    def test_plain_line_needs_the_binary_check_too(self):
        # #1008: examples/bigframe-unwind (plain `cargo fv`, rust-lld) printed `0 of 1` and
        # passed. Its executable is outside the binary check for a stated reason: the line is
        # green only with the executable's entry in the known-unverified list
        reason = ("not verified: link-check stopped before the binary check: link-proof skipped 1 function(s) of "
                  "the region: __fv_e90dc2697494__RNxC15bigframe_unwind12H1IxI06hs9Qw: unverified: outside "
                  "clif-subset-v2 E (the executable links Lean-compiled code that is unverified, so it is not the "
                  "proven program; `cargo fv report --functions` lists the unverified functions, and --lean-link "
                  "--verified keeps cg_clif's code for them)")
        funcs = "cargo fv: 103 of 103 functions compiled by the Lean backend (101 verified): your crate(s) 103 of 103\n"
        log = exe("bigframe-unwind", "bigframe_unwind", reason) + count(0, 1) + funcs + "SAME: 2 test outcomes identical (logs: /t)\n"
        ok, line = fv(log, False, fv_log=log)
        self.assertFalse(ok)
        self.assertIn("FAIL: not verified: bigframe-unwind/bigframe_unwind", line)
        ok, line = fv(log, False, [("bigframe-unwind/bigframe_unwind", "#581")], fv_log=log)
        self.assertTrue(ok, line)
        self.assertIn("known unverified (scripts/gate-known-unverified.txt): bigframe-unwind/bigframe_unwind #581", line)
        # no executable with Lean-compiled code: cargo fv prints no count line
        self.assertFalse(fv(SAME, False, fv_log="")[0])

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

    def test_list_applies_to_every_line(self):
        # also to a line that does not link with lean-ld (bigframe-unwind)
        self.assertTrue(fv(survey(), False, KNOWN)[0])
        self.assertFalse(fv(survey(bad=()), False, KNOWN)[0])
        self.assertFalse(fv(survey(), False)[0])

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


class PinnedCounts(unittest.TestCase):
    """#1004's residual: `N of N` passed with a smaller N. The executables and the Lean-compiled
    and verified functions of every example are pinned (scripts/gate-expected-counts.txt)."""

    BIG = ("cargo fv: binary /w/target/fv/plain/aarch64-unknown-linux-musl/debug/build/bigframe-unwind/938e46b67ec0fe2f/out/"
           "bigframe_unwind-938e46b67ec0fe2f: verified: E2E.Binary.binary_correct holds for its 75 Lean-compiled functions\n"
           + count(1, 1) + "cargo fv: 103 of 103 functions compiled by the Lean backend (101 verified): your crate(s)\n"
           "SAME: 2 test outcomes identical (logs: /t)\n")

    def test_equal(self):
        ok, line = fv(survey(bad=()), True, pinned=PINNED)
        self.assertTrue(ok, line)
        self.assertIn("pinned (scripts/gate-expected-counts.txt): 8 executables, 3251 Lean-compiled, 3251 verified", line)

    def test_fewer_executables(self):
        # a crate whose codegen units all fell back to cg_clif: its executables have no
        # Lean-compiled code and leave the binary check; the rest is still N of N
        log = "".join(exe(c, c) + exe(c, "values") for c in ("a_arith", "b_slices", "c_structs_enums")) + count(6, 6) + SAME
        self.assertTrue(fv(log, True)[0])
        ok, line = fv(log, True, pinned=PINNED)
        self.assertFalse(ok)
        self.assertIn("FAIL: executables through the binary check: 6, pinned 8 (exact; an intended change sets "
                      "`survey  6  3251  3251` in scripts/gate-expected-counts.txt in the same PR)", line)

    def test_more_executables(self):
        ok, line = fv(survey(bad=()), True, pinned=(7, 3251, 3251))
        self.assertFalse(ok)
        self.assertIn("FAIL: executables through the binary check: 8, pinned 7", line)

    def test_drop_is_a_regression(self):
        ok, line = fv(survey(bad=()), True, pinned=(8, 3251, 3260))
        self.assertFalse(ok)
        self.assertIn("FAIL: verified functions: 3251 is below the pinned 3260 (a regression)", line)
        self.assertNotIn("Lean backend: 3251 is", line)
        ok, line = fv(survey(bad=()), True, pinned=(8, 3252, 3251))
        self.assertFalse(ok)
        self.assertIn("FAIL: functions compiled by the Lean backend: 3251 is below the pinned 3252 (a regression)", line)

    def test_rise_must_be_recorded(self):
        ok, line = fv(survey(bad=()), True, pinned=(8, 3251, 3200))
        self.assertFalse(ok)
        self.assertIn("FAIL: verified functions: 3251 is above the pinned 3200: record the rise in the same PR "
                      "(`survey  8  3251  3251` in scripts/gate-expected-counts.txt)", line)
        self.assertFalse(fv(survey(bad=()), True, pinned=(8, 3000, 3000))[0])

    def test_lean_and_verified_are_two_pins(self):
        # plain cargo fv links unverified Lean code: 103 Lean-compiled, 101 verified
        for pinned, ok in (((1, 103, 101), True), ((1, 103, 100), False), ((1, 103, 102), False),
                           ((1, 102, 101), False), ((1, 104, 101), False), ((2, 103, 101), False)):
            self.assertEqual(fv(self.BIG, False, pinned=pinned, example="bigframe-unwind")[0], ok, pinned)

    def test_no_pins_for_the_example(self):
        ok, line = gc.cargo_fv("survey", survey(bad=()), True, (), LEAN_LD, None)
        self.assertFalse(ok)
        self.assertIn("FAIL: no pinned counts for survey (scripts/gate-expected-counts.txt)", line)

    def test_missing_count_fails_once(self):
        # no binary check line: its own failure, no second one from the pins
        ok, line = fv(SAME, True, pinned=PINNED)
        self.assertFalse(ok)
        self.assertEqual(line.count("FAIL:"), 1, line)

    def test_read_expected(self):
        self.assertEqual(gc.read_expected(PINS, "survey"), (PINNED, []))
        self.assertEqual(gc.read_expected(PINS, "deps"), (None, []))
        for bad in ("survey 8 3251\n", "survey 8 3251 3251 1\n", "survey 8 many 3251\n", "survey -8 3251 3251\n",
                    "survey 8 3251 3252\n", "survey 8 3251 3251\nsurvey 8 3251 3251\n"):
            self.assertEqual(len(gc.read_expected(bad, "fv-demo")[1]), 1, bad)

    def test_checked_in_file(self):
        # every gate line's example has its pins, and the file parses
        text = (HERE / "gate-expected-counts.txt").read_text()
        for e in ("fv-demo", "survey", "deps", "bigframe-unwind"):
            pinned, errors = gc.read_expected(text, e)
            self.assertEqual(errors, [])
            self.assertTrue(pinned and pinned[0] > 0 and pinned[1] >= pinned[2] > 0, e)

    def test_summary(self):
        env = {"GITHUB_SERVER_URL": "https://github.com", "GITHUB_REPOSITORY": "eth-act/clifv"}
        md = gc.summary("survey", survey(), KNOWN, PINNED, env)
        self.assertIn("| executables through the binary check | 8 | 8 | equal |", md)
        self.assertIn("| verified functions | 3251 | 3251 | equal |", md)
        self.assertNotIn("This run's line", md)
        self.assertIn("- `b_slices/values`: https://github.com/eth-act/clifv/issues/1003: not verified: 3 of 365", md)
        md = gc.summary("survey", survey(bad=()), [], (9, 3251, 3200), {})
        self.assertIn("| executables through the binary check | 9 | 8 | **-1: must be equal** |", md)
        self.assertIn("| verified functions | 3200 | 3251 | **+51: record the rise in this PR** |", md)
        self.assertIn("This run's line: `survey  8  3251  3251`", md)
        self.assertNotIn("Known unverified", md)
        md = gc.summary("survey", survey(bad=()), [], (8, 3300, 3300), {})
        self.assertIn("| verified functions | 3300 | 3251 | **-49: a regression** |", md)
        self.assertIn("**missing**", gc.summary("survey", SAME, [], None, {}))
        # outside CI the issue is named, not linked
        self.assertIn("- `b_slices/values`: #1003: not verified", gc.summary("survey", survey(), KNOWN, PINNED, {}))


class CommandLine(unittest.TestCase):
    def run_script(self, *a):
        return subprocess.run([sys.executable, str(HERE / "gate-line-check.py"), *map(str, a)], capture_output=True, text=True)

    def test_cargo_fv(self):
        with tempfile.TemporaryDirectory() as t:
            t = pathlib.Path(t)
            log, known, fvlog, pins = t / "survey.log", t / "known.txt", t / "fv.log", t / "pins.txt"
            log.write_text(survey())
            known.write_text(LIST)
            fvlog.write_text(LEAN_LD)
            pins.write_text(PINS)

            def run(example, *a, known=known, pins=pins):
                return self.run_script("cargo-fv", example, "--known", known, "--expected", pins, *a)

            r = run("survey", "--lean-link", log, fvlog)
            self.assertEqual((r.returncode, len(r.stdout.splitlines())), (0, 1), r.stdout)
            # the list is per example: the same log under another example's name is red
            r = run("fv-demo", "--lean-link", log, fvlog)
            self.assertEqual(r.returncode, 1)
            self.assertIn("FAIL: not verified: b_slices/values", r.stdout)
            # cargo fv's own log decides too; a lean-ld link is asked for with --lean-link only
            fvlog.write_text(NO_LEAN_LD)
            self.assertEqual(run("survey", "--lean-link", log, fvlog).returncode, 1)
            fvlog.write_text("")
            self.assertEqual(run("survey", "--lean-link", log, fvlog).returncode, 1)
            self.assertEqual(run("survey", log, fvlog).returncode, 0)
            fvlog.write_text(LEAN_LD)
            # an unreadable list line is red for every example
            known.write_text(LIST + "survey oops\n")
            self.assertEqual(run("survey", "--lean-link", log, fvlog).returncode, 1)
            known.write_text(LIST)
            # the pins: another count, an unreadable line, no line for the example
            pins.write_text(PINS.replace("survey  8", "survey  9"))
            r = run("survey", "--lean-link", log, fvlog)
            self.assertEqual(r.returncode, 1)
            self.assertIn("FAIL: executables through the binary check: 8, pinned 9", r.stdout)
            pins.write_text(PINS + "deps 4 many 1\n")
            self.assertEqual(run("survey", "--lean-link", log, fvlog).returncode, 1)
            pins.write_text("fv-demo  8  3251  3251\n")
            r = run("survey", "--lean-link", log, fvlog)
            self.assertEqual(r.returncode, 1)
            self.assertIn("FAIL: no pinned counts for survey", r.stdout)
            pins.write_text(PINS)
            # --summary appends the Markdown of the counts and of the known-unverified executables
            md = t / "summary.md"
            md.write_text("before\n")
            self.assertEqual(run("survey", "--lean-link", "--summary", md, log, fvlog).returncode, 0)
            text = md.read_text()
            self.assertTrue(text.startswith("before\n### cargo fv counts: survey\n"), text)
            self.assertIn("### Known unverified executables: survey", text)
            # a missing log, list or pins file is a failure, not a pass
            self.assertEqual(run("survey", "--lean-link", str(log) + ".absent", fvlog).returncode, 1)
            self.assertEqual(run("survey", "--lean-link", log, str(fvlog) + ".absent").returncode, 1)
            self.assertEqual(run("survey", "--lean-link", log, fvlog, known=str(known) + ".absent").returncode, 1)
            self.assertEqual(run("survey", "--lean-link", log, fvlog, pins=str(pins) + ".absent").returncode, 1)

    def test_default_files(self):
        # without --known and --expected the checked-in files apply (a log with deps' pinned counts)
        e, lean, verified = gc.read_expected((HERE / "gate-expected-counts.txt").read_text(), "deps")[0]
        funcs = f"cargo fv: {lean} of {lean} functions compiled by the Lean backend ({verified} verified): your crate(s)\n"
        same = "SAME: 16 test outcomes identical (logs: /t)\n"
        with tempfile.TemporaryDirectory() as t:
            log, fvlog = pathlib.Path(t) / "deps.log", pathlib.Path(t) / "fv.log"
            fvlog.write_text(LEAN_LD)
            log.write_text(exe("deps-demo", "deps_demo") * e + count(e, e) + funcs + same)
            self.assertEqual(self.run_script("cargo-fv", "deps", "--lean-link", log, fvlog).returncode, 0)
            log.write_text(exe("deps-demo", "deps_demo") * (e - 1) + exe("deps-demo", "deps_demo", "not verified: x") + count(e - 1, e) + funcs + same)
            self.assertEqual(self.run_script("cargo-fv", "deps", "--lean-link", log, fvlog).returncode, 1)
            log.write_text(exe("deps-demo", "deps_demo") * (e - 1) + count(e - 1, e - 1) + funcs + same)
            r = self.run_script("cargo-fv", "deps", "--lean-link", log, fvlog)
            self.assertEqual(r.returncode, 1)
            self.assertIn(f"pinned {e} (exact", r.stdout)
            r = self.run_script("cargo-fv", "no-such-example", "--lean-link", log, fvlog)
            self.assertIn("FAIL: no pinned counts for no-such-example", r.stdout)

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
        for a in ([], ["cargo-fv"], ["cargo-fv", "a.log"], ["cargo-fv", "a.log", "fv.log"], ["deps.log"],
                  ["float-spec", "x.log"], ["arm-fault-cosim", "--lean-link", "x.log"], ["arm-fault-cosim", "a.log", "b.log"],
                  ["cargo-fv", "survey", "a.log", "b.log", "c.log"], ["cargo-fv", "survey", "a.log", "fv.log", "--known"],
                  ["cargo-fv", "survey", "--lean-link", "--lean-link", "a.log", "fv.log"],
                  ["cargo-fv", "survey", "--known", "k", "--known", "k", "a.log", "fv.log"],
                  ["cargo-fv", "", "a.log", "fv.log"], ["cargo-fv", "survey", "--verified", "a.log", "fv.log"],
                  ["cargo-fv", "--binary-check", "survey", "a.log", "fv.log"]):
            self.assertEqual(self.run_script(*a).returncode, 2, a)


if __name__ == "__main__":
    unittest.main()
