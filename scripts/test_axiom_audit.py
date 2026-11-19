import importlib.util, pathlib, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("axiom_audit", HERE / "axiom-audit.py")
aa = importlib.util.module_from_spec(spec)
spec.loader.exec_module(aa)

# Lean 4.34.1's output for theorems of a probe module (#1133): `clean1 : True := trivial`,
# `std1` (Classical.em), `sorry1` (sorry), `custom1` (a declared `axiom myAx : False`), `native1`,
# `native1_ext`, `nativeW` (native_decide), `rb` (Lean.ofReduceBool), LONG (sorry, wraps) and
# LONGN (three native_decide, wraps).
LONG = "ProbeNS.aVeryLongTheoremNameThatIsDefinitelyLongEnoughToForceLeanToWrapTheAxiomListOverSeveralLinesOfOutput"
LONGN = LONG + "Native"
OUT = {
    "clean1": "'clean1' does not depend on any axioms\n",
    "std1": "'std1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
    "sorry1": "'sorry1' depends on axioms: [sorryAx]\n",
    "custom1": "'custom1' depends on axioms: [myAx]\n",
    "native1": "'native1' depends on axioms: [native1._native.native_decide.ax_1_1]\n",
    "native1_ext": "'native1_ext' depends on axioms: [native1_ext._native.native_decide.ax_1_1]\n",
    "nativeW": "'nativeW' depends on axioms: [nativeW._native.native_decide.ax_1_1]\n",
    "rb": "'rb' depends on axioms: [Lean.ofReduceBool, Lean.trustCompiler]\n",
    LONG: f"'{LONG}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound,\n sorryAx]\n",
    LONGN: f"'{LONGN}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound,\n"
           + ",\n".join(f" {LONGN}._native.native_decide.ax_1_{k}" for k in (1, 2, 3)) + "]\n",
}
NATIVES = {"native1": 1, "native1_ext": 1, "nativeW": 1, LONGN: 3}
UNKNOWN = "/x/probe.lean:3:14: error(lean.unknownIdentifier): Unknown constant `doesNotExist`\n"
BAD = {"sorry1": "sorryAx", "custom1": "myAx", "native1": "native1._native.native_decide.ax_1_1",
       "rb": "Lean.ofReduceBool", LONG: "sorryAx"}


def p(name, witness=False):
    return f"#print axioms {name}" + (" -- witness: native_decide" if witness else "")


def checked(*names):
    return "".join(f"axiom-audit native: '{n}' {NATIVES.get(n, 0)} re-evaluated\n" for n in names)


def verdict(lines, outs, rc=0, native=None):
    """audit() of a file made of `lines` whose Lean output is `outs` in order; with witnesses, the
    native check lines of `native` (default: every marked line's theorem, in order) follow."""
    text = "import ProbeDefs\n" + "\n".join(lines) + "\n"
    witnesses = [n for n, w in aa.commands(text)[0] if w]
    out = "".join(outs)
    if witnesses:
        out += checked(*witnesses) if native is None else native
    return aa.audit(text, out, rc, bool(witnesses))


class Attribution(unittest.TestCase):
    def test_issue_1133_witness_after_axiom_free_theorem(self):
        ok, summary, _ = verdict([p("clean1"), p("nativeW", True), p("std1")],
                                 [OUT["clean1"], OUT["nativeW"], OUT["std1"]])
        self.assertTrue(ok, summary)
        self.assertIn("native_reevaluated=1", summary)

    def test_bad_theorem_after_and_before_axiom_free_one(self):
        for bad, ax in BAD.items():
            for order in ([("clean1"), bad], [bad, "clean1"]):
                with self.subTest(bad=bad, order=order):
                    ok, summary, _ = verdict([p(n) for n in order], [OUT[n] for n in order])
                    self.assertFalse(ok)
                    self.assertIn(f"other_axioms=[{bad}: {ax}", summary)

    def test_wrapped_axiom_lists(self):
        self.assertFalse(verdict([p("clean1"), p(LONG)], [OUT["clean1"], OUT[LONG]])[0])
        self.assertFalse(verdict([p("clean1"), p(LONGN)], [OUT["clean1"], OUT[LONGN]])[0])
        ok, summary, _ = verdict([p("clean1"), p(LONGN, True), p("std1")],
                                 [OUT["clean1"], OUT[LONGN], OUT["std1"]])
        self.assertTrue(ok, summary)
        self.assertIn("native_reevaluated=3", summary)

    def test_witness_mark_is_per_command_not_per_name_prefix(self):
        for marked, plain in (("native1", "native1_ext"), ("native1_ext", "native1")):
            with self.subTest(marked=marked):
                ok, summary, _ = verdict([p(marked, True), p(plain)], [OUT[marked], OUT[plain]])
                self.assertFalse(ok)
                self.assertIn(f"other_axioms=[{plain}: {plain}._native", summary)

    def test_unknown_constant(self):
        for bad in BAD:
            with self.subTest(bad=bad):
                ok, summary, _ = verdict([p("clean1"), p("doesNotExist"), p(bad)],
                                         [OUT["clean1"], UNKNOWN, OUT[bad]], rc=1)
                self.assertFalse(ok)
                self.assertIn("2 results for 3 commands", summary)
        # even if Lean's exit code and error text were lost, the missing result fails
        self.assertFalse(verdict([p("clean1"), p("doesNotExist")], [OUT["clean1"]])[0])

    def test_duplicated_names(self):
        self.assertFalse(verdict([p("native1", True), p("native1")], [OUT["native1"]] * 2)[0])
        self.assertFalse(verdict([p("clean1"), p("native1"), p("native1", True)],
                                 [OUT["clean1"]] + [OUT["native1"]] * 2)[0])
        self.assertFalse(verdict([p("sorry1"), p("sorry1")], [OUT["sorry1"]] * 2)[0])

    def test_names_resolved_by_open_and_root(self):
        inner = "'ProbeNS.inner' does not depend on any axioms\n"
        ok, summary, _ = verdict(["open ProbeNS", p("inner"), p("_root_.clean1")], [inner, OUT["clean1"]])
        self.assertTrue(ok, summary)
        ok, summary, _ = verdict([p("clean1"), p("std1")], [OUT["std1"], OUT["clean1"]])
        self.assertFalse(ok)
        self.assertIn("result 1 names 'std1', command 1 names clean1", summary)


class Commands(unittest.TestCase):
    def test_mark_inside_block_comment_does_not_count(self):
        for opener in ("/-", "/- outer /- inner -/"):
            with self.subTest(opener=opener):
                ok, summary, _ = verdict([opener, p("native1", True), "-/", "  " + p("native1")],
                                         [OUT["native1"]])
                self.assertFalse(ok)
                self.assertIn("other_axioms=[native1: native1._native", summary)

    def test_commented_out_commands(self):
        self.assertTrue(verdict(["-- " + p("sorry1"), p("clean1")], [OUT["clean1"]])[0])
        self.assertFalse(verdict(["/-", p("clean1"), "-/", "  " + p("sorry1")], [OUT["sorry1"]])[0])

    def test_mark_must_be_exact(self):
        line = p("native1") + " -- witness: native_decide_not_really"
        self.assertFalse(verdict([line], [OUT["native1"]])[0])
        ok, summary, _ = verdict([p("native1", True) + " (fixed compiler data)"], [OUT["native1"]])
        self.assertTrue(ok, summary)

    def test_file_checking_by_other_commands_only(self):
        # e.g. scripts/audit/stock-logical-extr.lean: a `run_cmd` that throws on an unexpected axiom
        lines = ["run_cmd do", '  logInfo "SCAN 3"']
        ok, summary, _ = verdict(lines, ["SCAN 3\n"])
        self.assertTrue(ok, summary)
        self.assertIn("theorems 0/0", summary)
        out = "/x/probe.lean:2:0: error: unexpected axiom sorryAx in A.b\n"
        self.assertFalse(verdict(lines, [out], rc=1)[0])

    def test_two_commands_on_one_line(self):
        ok, summary, _ = verdict([p("clean1") + " " + p("sorry1")], [OUT["clean1"], OUT["sorry1"]])
        self.assertFalse(ok)
        self.assertIn("not alone on its line", summary)

    def test_result_text_printed_by_another_command(self):
        lines = ["/-", p("native1"), "-/", '#eval IO.println "\'native1\' does not depend on any axioms"']
        self.assertFalse(verdict(lines, ["'native1' does not depend on any axioms\n"])[0])
        # a result message that does not start a line is not a result, and fails
        self.assertFalse(verdict([p("clean1")], ["x " + OUT["clean1"]])[0])

    def test_strip_comments(self):
        text = 'a -- b /- c\nd /- e /- f -/ g -/ h\n"i -- j" k /-\nl\n-/ m\n'
        self.assertEqual(aa.strip_comments(text).split(), ["a", "d", "h", "k", "m"])
        self.assertEqual(aa.strip_comments(text).count("\n"), text.count("\n"))


class Native(unittest.TestCase):
    LINES = [p("clean1"), p("nativeW", True), p(LONGN, True)]
    OUTS = [OUT["clean1"], OUT["nativeW"], OUT[LONGN]]

    def test_checked(self):
        ok, summary, _ = verdict(self.LINES, self.OUTS)
        self.assertTrue(ok, summary)
        self.assertIn("native_reevaluated=4", summary)

    def test_check_lines_must_match_the_witnesses(self):
        for native in ("", checked("nativeW"), checked(LONGN, "nativeW"),
                       checked("nativeW", "nativeW", LONGN),
                       checked("nativeW") + f"axiom-audit native: '{LONGN}' 2 re-evaluated\n"):
            with self.subTest(native=native):
                self.assertFalse(verdict(self.LINES, self.OUTS, native=native)[0])

    def test_unchecked_native_axioms_fail(self):
        text = "\n".join(self.LINES) + "\n"
        ok, summary, _ = aa.audit(text, "".join(self.OUTS), 0, False)
        self.assertFalse(ok)
        self.assertIn("not re-evaluated", summary)

    def test_failed_reevaluation(self):
        # a declared `axiom fake2._native.native_decide.ax_1 : decide (1 = 2) = true` used by a witness
        out = ("'fake2W' depends on axioms: [fake2._native.native_decide.ax_1]\n"
               "/x/.lake/axiom-audit/h.lean:29:0: error: axiom-audit: native axiom "
               "fake2._native.native_decide.ax_1 states `e = true` for an `e` that evaluates to false\n")
        self.assertFalse(aa.audit(p("fake2W", True) + "\n", out, 1, True)[0])

    def test_native_source(self):
        src = aa.native_source("import A\n" + p("w", True) + "\n" + p("v") + "\n", ["w"])
        self.assertTrue(src.startswith("import Lean\nimport A\n"))
        self.assertIn('elab "#axiom_audit_native" ids:ident* : command', src)
        self.assertTrue(src.endswith("\n#axiom_audit_native w\n"))


class AuditFiles(unittest.TestCase):
    def test_every_audit_file_has_commands_alone_on_their_lines(self):
        files = sorted((HERE / "audit").glob("*.lean"))
        self.assertTrue(files)
        for f in files:
            with self.subTest(file=f.name):
                cmds, occurrences = aa.commands(f.read_text())
                self.assertEqual(occurrences, len(cmds))


if __name__ == "__main__":
    unittest.main()
