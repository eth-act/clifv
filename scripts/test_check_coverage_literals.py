"""Unit tests of scripts/check-coverage-literals.py, and the lint on lean-link's driver (#1104).

Run by the Quick checks workflow (`python3 -m unittest discover -s scripts -p 'test_*.py'`), so a
theorem-name literal added to `FVTest/Link/LeanLinkMain.lean` outside the claim table fails there.
"""

import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("ccl", HERE / "check-coverage-literals.py")
ccl = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ccl)


class CoverageLiterals(unittest.TestCase):
    def test_lean_link_main_has_none(self):
        src = (HERE.parent / "FVTest/Link/LeanLinkMain.lean").read_text()
        self.assertEqual(ccl.hits(src), [])

    def test_string_literal_is_found(self):
        src = 'def f := IO.println s!"coverage: Link.compileExe_correct, {x}"\n'
        self.assertEqual(ccl.hits(src), [(1, "Link.compileExe_correct")])

    def test_interpolated_literal_is_found(self):
        src = 'def f := s!"a {thm "compileExe_total_ld"} b"\n'
        self.assertEqual([t for _, t in ccl.hits(src)], ["compileExe_total_ld"])

    def test_other_name_patterns(self):
        src = 'def f := "Front.bundle_correct_rawTCp E2E.X.legalProg_refinesT Link.Ld.file0OkB_ld"\n'
        self.assertEqual(len(ccl.hits(src)), 3)

    def test_comments_are_ignored(self):
        src = ("/-! doc: `compileExe_correct` /- nested `x_total` -/ still -/\n"
               "-- `attempt_correct`\n"
               "/-- `attemptT_correct` -/\n"
               "def f := 1 -- compileExeT_correct\n")
        self.assertEqual(ccl.hits(src), [])

    def test_comment_markers_inside_strings(self):
        src = 'def f := "-- not a comment compileExe_correct"\n'
        self.assertEqual(len(ccl.hits(src)), 1)

    def test_line_numbers_kept(self):
        src = '/-\n\n-/\nx\n"a_correct"\n'
        self.assertEqual(ccl.hits(src), [(5, "a_correct")])


if __name__ == "__main__":
    unittest.main()
