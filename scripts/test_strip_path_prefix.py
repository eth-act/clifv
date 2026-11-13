import importlib.util, pathlib, subprocess, sys, tempfile, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("strip_path_prefix", HERE / "strip-path-prefix.py")
sp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sp)

EXE = "examples/survey/target/regen/fv/plain/aarch64-unknown-linux-musl/debug/build/a_arith/53103433804e745e/out/values-53103433804e745e"
DOC = '"Crate-level instance") for the executable\n\n  {root}/' + EXE + "\n\nThe program `P` is the 58 functions\n"


class Strip(unittest.TestCase):
    def test_plain_root(self):
        out, left = sp.strip(DOC.format(root="/home/runner/work/clifv/clifv"), "/home/runner/work/clifv/clifv/")
        self.assertEqual(out, DOC.replace("{root}/", ""))
        self.assertFalse(left)

    def test_root_with_pattern_characters(self):
        # review finding (CiGate2Review 3): `sed "s|$ROOT/||g"` read the checkout path as a regular
        # expression (`clif[v]` did not match itself) and as its own delimiter (`|`)
        for root in ("/home/user/clif[v]", "/w/a|b", "/w/a.b*c", "/w/a&b", "/w/a\\1b", "/w/a b", "/w/$x^y"):
            out, left = sp.strip(DOC.format(root=root), root + "/")
            self.assertEqual(out, DOC.replace("{root}/", ""), root)
            self.assertFalse(left, root)

    def test_literal_not_pattern(self):
        # `.` is a dot: another path of the same shape stays
        text = DOC.format(root="/w/aXb")
        self.assertEqual(sp.strip(text, "/w/a.b/"), (text, False))

    def test_root_left_in_another_form(self):
        # the path without the slash this script removes (e.g. at the end of a sentence)
        out, left = sp.strip("built in /w/clifv.\n", "/w/clifv/")
        self.assertTrue(left)


class CommandLine(unittest.TestCase):
    def run_script(self, *a):
        return subprocess.run([sys.executable, str(HERE / "strip-path-prefix.py"), *map(str, a)], capture_output=True, text=True)

    def test_files(self):
        with tempfile.TemporaryDirectory() as t:
            t = pathlib.Path(t)
            root = "/home/user/clif[v]|x"
            a, b, c = t / "A.lean", t / "B.lean", t / "C.lean"
            a.write_text(DOC.format(root=root))
            b.write_text("no path here\n")
            self.assertEqual(self.run_script(root + "/", a, b).returncode, 0)
            self.assertEqual(a.read_text(), DOC.replace("{root}/", ""))
            self.assertEqual(b.read_text(), "no path here\n")
            # a path the rewrite leaves, and a missing file, are errors; the other files are done
            a.write_text(DOC.format(root=root))
            c.write_text(f"built in {root}.\n")
            r = self.run_script(root + "/", c, t / "absent.lean", a)
            self.assertEqual(r.returncode, 1)
            self.assertIn("C.lean still names /home/user/clif[v]|x", r.stderr)
            self.assertIn("absent.lean", r.stderr)
            self.assertEqual(a.read_text(), DOC.replace("{root}/", ""))

    def test_usage(self):
        for a in ([], ["/w/"], ["/", "x"], ["", "x"]):
            self.assertEqual(self.run_script(*a).returncode, 2, a)


if __name__ == "__main__":
    unittest.main()
