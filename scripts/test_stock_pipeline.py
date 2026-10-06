"""Single-entrypoint orchestration tests; actual compiler integration is separate."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

PIPELINE = Path(__file__).with_name("stock-compiler-comparison.sh")


class PipelineTests(unittest.TestCase):
    def run_fixture(self, root, **overrides):
        scripts, binaries = root/"scripts",root/"bin"
        scripts.mkdir();binaries.mkdir()
        (root/"rust").mkdir()
        (root/"lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        (root/"rust/rust-toolchain.toml").write_text('[toolchain]\nchannel = "1.96.0"\n')
        (scripts/PIPELINE.name).write_text(PIPELINE.read_text())
        mocks = {
            "lean": '#!/usr/bin/env bash\nprintf "Lean (version 4.34.1)\\n"\n',
            "lake": '#!/usr/bin/env bash\nprintf "Lake with Lean 4.34.1\\n"\n',
            "git": '#!/usr/bin/env bash\nprintf "fixture-commit\\n"\n',
            "rustup": '#!/usr/bin/env bash\nif [[ ${FAIL_BUILD:-0} == 1 && $1 == run && $3 == cargo && $4 == build ]]; then exit 9; fi\nprintf "fixture Rust 1.96.0\\n"\n',
        }
        for name, source in mocks.items():
            path=binaries/name;path.write_text(source);path.chmod(0o755)
        (scripts/"prejit-export-build.sh").write_text("#!/usr/bin/env bash\nexit 0\n")
        (scripts/"test_stock_compiler_compare.py").write_text("import unittest\nclass Fixture(unittest.TestCase):\n def test_fixture(self): self.assertTrue(True)\n")
        (scripts/"test_stock_exporter.py").write_text("import unittest\nclass Fixture(unittest.TestCase):\n def test_fixture(self): self.assertTrue(True)\n")
        (scripts/"test_stock_pipeline.py").write_text("import unittest\nclass Fixture(unittest.TestCase):\n def test_fixture(self): self.assertTrue(True)\n")
        (scripts/"stock-compiler-compare.py").write_text('''import argparse,json,os
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--out');p.add_argument('--jobs');a=p.parse_args()
if os.environ.get('FAIL_COMPARISON')=='1': raise SystemExit(7)
out=Path(a.out);out.mkdir()
result={'progress':'finished','jobs':a.jobs,'allocator':os.environ.get('LEAN_REGALLOC'),
 'rustflags':os.environ.get('RUSTFLAGS'),'target_dir':os.environ.get('CARGO_TARGET_DIR')}
(out/'results.json').write_text(json.dumps(result));(out/'summary.md').write_text('fixture')
raise SystemExit(10)
''')
        env=os.environ.copy()
        env.pop("BLESS",None)
        env.update(PATH=str(binaries)+os.pathsep+env["PATH"], LEAN_BIN_DIR=str(binaries),
            FV_COMPARE_MEMCAP="0",LEAN_REGALLOC="wrong-allocator",RUSTFLAGS="wrong-flags",CARGO_TARGET_DIR="wrong-target")
        env.update(overrides)
        return subprocess.run(["bash",str(scripts/PIPELINE.name),"--out","target/result","--jobs","3"],
            cwd=root,env=env,capture_output=True,text=True)

    def test_complete_measurement_preserves_nonagreement_exit_and_pins_tools(self):
        with tempfile.TemporaryDirectory(prefix="stock-pipeline-test-") as temp:
            root=Path(temp);result=self.run_fixture(root)
            self.assertEqual(result.returncode,10,result.stderr)
            self.assertIn("Measurement complete",result.stdout)
            data=json.loads((root/"target/result/results.json").read_text())
            self.assertEqual(data["allocator"],str(root/"rust/target/release/lean-regalloc"))
            self.assertEqual(data["jobs"],"3")
            self.assertIsNone(data["rustflags"]);self.assertIsNone(data["target_dir"])
            logs=root/"target/result.build-logs"
            for name in ("versions.txt","allocator.log","lean-backend.log","stock-exporter.log","validation.log","exporter-validation.log","comparison.log"):
                self.assertTrue((logs/name).exists(),name)
            self.assertIn("--locked",(logs/"allocator.command").read_text())
            self.assertIn("1.96.0",(logs/"allocator.command").read_text())

    def test_build_failure_stops_before_measurement(self):
        with tempfile.TemporaryDirectory(prefix="stock-pipeline-test-") as temp:
            root=Path(temp);result=self.run_fixture(root,FAIL_BUILD="1")
            self.assertEqual(result.returncode,9,result.stderr)
            self.assertFalse((root/"target/result/results.json").exists())
            self.assertNotIn("Measurement complete",result.stdout)

    def test_comparison_crash_is_not_a_completed_measurement(self):
        with tempfile.TemporaryDirectory(prefix="stock-pipeline-test-") as temp:
            root=Path(temp);result=self.run_fixture(root,FAIL_COMPARISON="1")
            self.assertEqual(result.returncode,7,result.stderr)
            self.assertNotIn("Measurement complete",result.stdout)

    def test_help_and_bad_arguments_need_no_compilers(self):
        result=subprocess.run(["bash",PIPELINE,"--help"],capture_output=True,text=True)
        self.assertEqual(result.returncode,0)
        for args in (("--jobs","0"),("--out",),("--unknown",)):
            result=subprocess.run(["bash",PIPELINE,*args],capture_output=True,text=True)
            self.assertEqual(result.returncode,2,args)

    def test_bless_is_rejected(self):
        env=os.environ.copy();env["BLESS"]="1"
        result=subprocess.run(["bash",PIPELINE],env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,2)
        self.assertIn("BLESS must be unset",result.stderr)


if __name__ == "__main__":
    unittest.main()
