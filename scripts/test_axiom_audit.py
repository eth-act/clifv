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
NONCE = "0123456789abcdef0123456789abcdef"


def p(name, witness=False):
    return f"#print axioms {name}" + (" -- witness: native_decide" if witness else "")


def source(lines):
    return "import ProbeDefs\n" + "\n".join(lines) + "\n"


def block(text, phase, nonce=NONCE, deferred=()):
    """The lines LEAN_CHECK's `phase` block prints when every command passes it."""
    cmds = aa.commands(text)[0]
    return ("".join(f"axiom-audit {nonce} {phase} {k} deferred\n" if k in deferred else
                    f"axiom-audit {nonce} {phase} {k} '{aa.full_name(name)}' native={NATIVES.get(name, 0) if w else 0}\n"
                    for k, (name, w) in enumerate(cmds))
            + f"axiom-audit {nonce} {phase} done {len(cmds)}\n")


def verdict(lines, outs, rc=0, top=None, end=None):
    """audit() of a file made of `lines` whose `#print axioms` output is `outs`, between
    LEAN_CHECK's blocks `top` and `end` (default: those of a passing check)."""
    text = source(lines)
    out = ((block(text, "top") if top is None else top) + "".join(outs)
           + (block(text, "end") if end is None else end))
    return aa.audit(text, out, rc, NONCE)


class Attribution(unittest.TestCase):
    def test_issue_1133_witness_after_axiom_free_theorem(self):
        ok, summary, _ = verdict([p("clean1"), p("nativeW", True), p("std1")],
                                 [OUT["clean1"], OUT["nativeW"], OUT["std1"]])
        self.assertTrue(ok, summary)
        self.assertIn("native=1", summary)

    def test_bad_theorem_after_and_before_axiom_free_one(self):
        for bad, ax in BAD.items():
            for order in (["clean1", bad], [bad, "clean1"]):
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
        self.assertIn("native=3", summary)

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

    def test_names_are_full_names(self):
        self.assertTrue(verdict([p("_root_.clean1")], [OUT["clean1"]])[0])
        inner = "'ProbeNS.inner' does not depend on any axioms\n"
        ok, summary, _ = verdict(["open ProbeNS", p("inner")], [inner])
        self.assertFalse(ok)
        self.assertIn("result 1 names 'ProbeNS.inner', command 1 names inner", summary)
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

    def test_strip_comments(self):
        text = 'a -- b /- c\nd /- e /- f -/ g -/ h\n"i -- j" k /-\nl\n-/ m\n'
        self.assertEqual(aa.strip_comments(text).split(), ["a", "d", "h", "k", "m"])
        self.assertEqual(aa.strip_comments(text).count("\n"), text.count("\n"))
        text = "def q := '\"'\ndef r := r#\"x \" -- y\"#\n" + p("t'") + "\n"
        self.assertEqual(aa.commands(text), ([("t'", False)], 1))


class Forged(unittest.TestCase):
    """The file's own commands print text that looks like results or like LEAN_CHECK's lines."""

    def test_forged_result_for_a_commented_out_command(self):
        lines = ["/-", p("native1"), "-/", '#eval IO.println "\'native1\' does not depend on any axioms"']
        self.assertFalse(verdict(lines, ["'native1' does not depend on any axioms\n"])[0])
        # a result message that does not start a line is not a result, and fails
        self.assertFalse(verdict([p("clean1")], ["x " + OUT["clean1"]])[0])

    def test_exit_before_the_end_block(self):
        # `#eval IO.println "'sorry1' does not depend on any axioms"`, `#exit`, `#print axioms sorry1`:
        # the forged result matches, the top block reports sorryAx, the end block never runs
        forged = "'sorry1' does not depend on any axioms\n"
        lines = ['#eval IO.println "\'sorry1\' does not depend on any axioms"', "#exit", p("sorry1")]
        err = "/x/f.lean:9:0: error: axiom-audit: 'sorry1' depends on the disallowed axiom sorryAx\n"
        self.assertFalse(verdict(lines, [forged], rc=1, top=err + block(source(lines), "top"), end="")[0])
        # even a clean theorem fails when the end block does not run, or prints another nonce
        lines = ["#exit", p("clean1")]
        self.assertFalse(verdict(lines, [OUT["clean1"]], end="")[0])
        self.assertFalse(verdict(lines, [OUT["clean1"]], end=block(source(lines), "end", nonce="f" * 32))[0])

    def test_check_lines_must_match_the_commands(self):
        lines = [p("clean1"), p("nativeW", True), p(LONGN, True)]
        outs = [OUT["clean1"], OUT["nativeW"], OUT[LONGN]]
        text = source(lines)
        top, end = block(text, "top").splitlines(keepends=True), block(text, "end")
        self.assertTrue(verdict(lines, outs)[0])
        for t in (top[:-1], top[1:], top[:1] + top[:], [top[1], top[0]] + top[2:],
                  [l.replace("native=3", "native=2") for l in top], [l.replace("done 3", "done 2") for l in top],
                  ["x " + top[0]] + top[1:], [top[0].replace("'clean1'", "'std1'")] + top[1:]):
            with self.subTest(top=t):
                self.assertFalse(verdict(lines, outs, top="".join(t))[0])
        for e in ("", end.replace("native=1", "native=0"), end + end, end.replace(" end ", " top ")):
            with self.subTest(end=e):
                self.assertFalse(verdict(lines, outs, end=e)[0])
        # forged extra lines with the right nonce (read from the file) fail too
        self.assertFalse(verdict(lines, outs, end=end + top[0])[0])

    def test_theorem_declared_by_the_file(self):
        # stock-logical-source-transfer-witness.lean: the top block cannot resolve it yet
        lines = ["theorem clean1 : True := trivial", p("clean1")]
        text = source(lines)
        top = block(text, "top", deferred={0})
        ok, summary, _ = verdict(lines, [OUT["clean1"]], top=top)
        self.assertTrue(ok, summary)
        self.assertIn("checked_after_the_file=1", summary)
        self.assertFalse(verdict(lines, [OUT["clean1"]], top=top, end="")[0])

    def test_lean_check_error_with_forged_clean_output(self):
        # `#guard_msgs` swallowed the real result and an `#eval` printed a clean one; the check in
        # Lean still sees sorryAx
        lines = [p("sorry1")]
        err = "/x/.lake/axiom-audit/f.lean:9:0: error: axiom-audit: 'sorry1' depends on the disallowed axiom sorryAx\n"
        self.assertFalse(verdict(lines, ["'sorry1' does not depend on any axioms\n"], rc=1,
                                 top=err + block(source(lines), "top"))[0])

    def test_native_axiom_declared_by_hand(self):
        # `axiom fake2._native.native_decide.ax_1 : decide ((1:Nat) = 2) = true` (or `: False`),
        # used by a marked witness: LEAN_CHECK stops with an error
        for why in ("is not declared inside fake2", "does not state `e = true`"):
            with self.subTest(why=why):
                err = f"/x/.lake/axiom-audit/h.lean:5:0: error: axiom-audit: native axiom fake2._native.native_decide.ax_1 {why}\n"
                out = "'fake2W' depends on axioms: [fake2._native.native_decide.ax_1]\n"
                self.assertFalse(verdict([p("fake2W", True)], [out], rc=1, top=err, end=err)[0])

    def test_check_source(self):
        src = aa.check_source("import A\n-- c\nimport B\nopen X\n" + p("w", True) + "\n" + p("_root_.v") + "\n", NONCE)
        top = f'#axiom_audit "{NONCE}" "top" "10" w _root_.v\n'
        self.assertTrue(src.startswith("import Lean\nimport A\n-- c\nimport B\n"))
        self.assertIn('elab "#axiom_audit " nonce:str phase:str flags:str ids:ident* : command', src)
        self.assertIn(top + "open X\n", src)
        self.assertTrue(src.endswith(f'\n#axiom_audit "{NONCE}" "end" "10" w _root_.v\n'))


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
