"""Check lowering diagnostics against the compiler's actual allocator request."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class LoweringTraceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.trace = ROOT / ".lake/build/bin/lean-backend-lowering-trace"
        cls.backend = ROOT / ".lake/build/bin/lean-backend"
        cls.allocator = ROOT / "rust/target/release/lean-regalloc"
        if not all(p.exists() for p in (cls.trace, cls.backend, cls.allocator)):
            raise unittest.SkipTest("build lean-backend, lean-backend-lowering-trace and lean-regalloc")

    def check_compilation(self, source, cleanup=True):
        with tempfile.TemporaryDirectory(prefix="stock-lowering_trace-") as tmp:
            directory = Path(tmp)
            input_path = directory / "input.clif"
            input_path.write_text(source)
            env = dict(os.environ, LEAN_REGALLOC=str(self.allocator))
            # Exercise the default cleanup mode and the explicit legacy diagnostic mode.
            flags = [] if cleanup else ["--no-dead-cleanup"]

            def compile_at(name):
                captured = directory / f"{name}.allocator.json"
                output = directory / f"{name}.o"
                result = subprocess.run(
                    [self.backend, input_path, output, *flags], cwd=ROOT,
                    env=dict(env, LEAN_REGALLOC_KEEP=str(captured)),
                    capture_output=True, text=True,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertNotIn("unsupported:", result.stderr)
                return output.read_bytes(), json.loads(captured.read_text())

            before, allocator = compile_at("before")
            report_path = directory / "trace.json"
            subprocess.run([self.trace, input_path, report_path, *flags], cwd=ROOT,
                           env=env, check=True, capture_output=True)
            report = json.loads(report_path.read_text())
            self.assertEqual(report["dead_cleanup"], cleanup)
            self.assertTrue(report["functions"])
            self.assertTrue(all(f["status"] == "lowered" for f in report["functions"]), report)
            self.assertEqual(
                [f["lowering"]["allocator_input"] for f in report["functions"]],
                allocator["functions"],
            )
            after, repeated_allocator = compile_at("after")
            self.assertEqual(before, after)
            self.assertEqual(allocator, repeated_allocator)
            return report

    def test_sparse_values_fusion_and_block_arguments(self):
        source = """function %fusion(i64, i64) -> i64 {
block0(v10: i64, v20: i64):
    v30 = bnot v20
    v40 = band v10, v30
    jump block1(v40)
block1(v50: i64):
    return v50
}
"""
        for cleanup in (True, False):
            with self.subTest(dead_cleanup=cleanup):
                self.check_compilation(source, cleanup)

    def test_i128_diagnostics_use_the_compilers_legalized_input(self):
        source = """function %wide(i64, i64) -> i128 {
block0(v0: i64, v1: i64):
    v2 = iconcat v0, v1
    return v2
}
"""
        for cleanup in (True, False):
            with self.subTest(dead_cleanup=cleanup):
                report = self.check_compilation(source, cleanup)
                self.assertEqual(report["legalization_accepted"], ["wide"])


class StockLoweringTraceTests(unittest.TestCase):
    def test_logging_preserves_stock_bytes_and_metadata(self):
        exporter = ROOT / "tools/prejit-export/target/debug/prejit-export"
        if not exporter.exists():
            self.skipTest("build prejit-export")
        source = ROOT / "third_party/wasmtime/cranelift/filetests/filetests/isa/aarch64/arithmetic.clif"
        env = dict(os.environ)
        env.pop("RUST_LOG", None)
        with tempfile.TemporaryDirectory(prefix="stock-lowering_logger-") as tmp:
            root = Path(tmp)
            plain = root / "plain"
            traced = root / "traced"

            def export(directory, settings):
                return subprocess.run(
                    [exporter, source, directory, "aarch64-unknown-linux-gnu", "--all-stages"],
                    cwd=ROOT, env=settings, capture_output=True, text=True, check=True,
                )

            quiet = export(plain, env)
            logged = export(traced, dict(env, RUST_LOG="cranelift_codegen::machinst::lower=trace"))
            self.assertNotIn("lower_clif_block", quiet.stderr)
            self.assertIn("lower_clif_block", logged.stderr)
            binaries = list(plain.rglob("*.bin"))
            self.assertTrue(binaries)
            for artifact in plain.rglob("*"):
                if artifact.is_file() and artifact.name != "manifest.json":
                    self.assertEqual(artifact.read_bytes(),
                                     (traced / artifact.relative_to(plain)).read_bytes(),
                                     str(artifact.relative_to(plain)))


if __name__ == "__main__":
    unittest.main()
