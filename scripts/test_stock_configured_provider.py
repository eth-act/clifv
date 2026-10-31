"""Check that configured compilation uses the proved production provider."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from byte_compare import ELF

ROOT = Path(__file__).resolve().parent.parent

MEMORY_CFG = """function %memory_cfg(i64) -> i32 {
block0(v0: i64):
    nop
    jump block1
block1:
    nop
    v2 = load.i32 notrap v0
    return v2
}
"""
MEMORY = """function %memory(i64) -> i32 {
block0(v0: i64):
    v2 = load.i32 notrap v0
    return v2
}
"""
RETAINED = """function %retained(i64) -> i64 {
block0(v0: i64):
    return v0
}
"""


class StockConfiguredProviderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.backend = ROOT / ".lake/build/bin/lean-backend"
        cls.trace = ROOT / ".lake/build/bin/lean-backend-lowering-trace"
        cls.allocator = ROOT / "rust/target/release/lean-regalloc"
        if not all(p.exists() for p in (cls.backend, cls.trace, cls.allocator)):
            raise unittest.SkipTest("build lean-backend, lean-backend-lowering-trace and lean-regalloc")
        cls.request = json.loads((ROOT / "scripts/testdata/stock-config-aarch64.json").read_text())

    def compile_at(self, directory, source, cleanup, configured, typed=False, request=None):
        directory.mkdir()
        input_path = directory / "input.clif"
        input_path.write_text(source)
        allocator_input = directory / "allocator.json"
        receipt_path = directory / "receipt.json"
        args = [self.backend, input_path, directory / "program.o", "--regalloc", "regalloc2"]
        if not cleanup:
            args.append("--no-dead-cleanup")
        if configured:
            requested = copy.deepcopy(self.request if request is None else request)
            requested["input_sha256"] = hashlib.sha256(input_path.read_bytes()).hexdigest()
            config = directory / "request.json"
            config.write_text(json.dumps(requested))
            args.extend(["--stock-config", config, "--config-receipt", receipt_path])
        env = dict(os.environ, LEAN_REGALLOC=str(self.allocator),
                   LEAN_REGALLOC_KEEP=str(allocator_input))
        env.pop("FV_PIPELINE_T", None)
        if typed:
            env["FV_PIPELINE_T"] = "1"
        result = subprocess.run(args, cwd=ROOT, env=env, capture_output=True, text=True)
        receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else None
        captured = json.loads(allocator_input.read_text())["functions"] if allocator_input.exists() else None
        return result, receipt, captured

    def check_provider(self, source, cleanup=True, typed=False, stock_selected=False):
        with tempfile.TemporaryDirectory(prefix="stock-configured-provider-") as tmp:
            directory = Path(tmp)
            plain, _, expected = self.compile_at(directory / "default", source, cleanup, False, typed)
            configured, receipt, actual = self.compile_at(directory / "configured", source, cleanup, True, typed)
            self.assertEqual(plain.returncode, 0, plain.stderr)
            self.assertEqual(configured.returncode, 0, configured.stderr)
            self.assertNotIn("unsupported:", configured.stderr)
            self.assertTrue(receipt["configuration_accepted"])
            self.assertFalse(receipt["function_rejections"])
            self.assertIn("experimental", receipt["proof_scope"])
            self.assertIsNotNone(expected)
            self.assertEqual(actual, expected)
            if not typed:
                trace_path = directory / "trace.json"
                flags = [] if cleanup else ["--no-dead-cleanup"]
                env = dict(os.environ)
                env.pop("FV_PIPELINE_T", None)
                traced = subprocess.run(
                    [self.trace, directory / "default/input.clif", trace_path,
                     "--stock-schedule", *flags], cwd=ROOT, env=env,
                    capture_output=True, text=True,
                )
                self.assertEqual(traced.returncode, 0, traced.stderr)
                report = json.loads(trace_path.read_text())
                self.assertEqual(report["dead_cleanup"], cleanup)
                self.assertEqual(len(report["functions"]), 1)
                row = report["functions"][0]
                self.assertEqual(row["status"], "lowered", row)
                self.assertEqual(len(expected), 1)
                lowering = row["lowering"]
                self.assertEqual(lowering["allocator_input"], expected[0])
                if not cleanup and stock_selected:
                    self.assertEqual(lowering["allocation_selected"],
                                     lowering["stock_schedule"]["selected"])
            name = source.splitlines()[0].split("%", 1)[1].split("(", 1)[0]
            plain_object = ELF(directory / "default/program.o")
            configured_object = ELF(directory / "configured/program.o")
            plain_symbol, plain_code = plain_object.function(name)
            configured_symbol, configured_code = configured_object.function(name)
            self.assertEqual(configured_code, plain_code)
            self.assertEqual(configured_object.function_relocations(configured_symbol, {}),
                             plain_object.function_relocations(plain_symbol, {}))

    def test_configured_compiler_uses_the_default_provider(self):
        fixtures = [(MEMORY_CFG, True), (MEMORY, True), (RETAINED, False)]
        fixtures.extend((MEMORY.replace('i32', ty), True) for ty in ('i8', 'i16', 'i64'))
        for op, types in (("uload8", ("i16", "i32", "i64")),
                          ("sload8", ("i16", "i32", "i64")),
                          ("uload16", ("i32", "i64")),
                          ("sload16", ("i32", "i64")),
                          ("uload32", ("i64",)), ("sload32", ("i64",))):
            fixtures.extend((MEMORY.replace("i32", ty).replace("load.", op + "."), True)
                            for ty in types)
        for source, stock_selected in fixtures:
            for cleanup in (False, True):
                with self.subTest(source=source.splitlines()[0], cleanup=cleanup):
                    self.check_provider(source, cleanup, stock_selected=stock_selected)

    def test_typed_pipeline_keeps_its_existing_provider(self):
        self.check_provider(MEMORY_CFG, cleanup=False, typed=True)

    def test_unsupported_settings_remain_rejected_before_allocation(self):
        request = copy.deepcopy(self.request)
        for flag in request["isa_flags"]:
            if flag["name"] == "use_bti":
                flag["value"] = "true"
        with tempfile.TemporaryDirectory(prefix="stock-configured-rejection-") as tmp:
            result, receipt, captured = self.compile_at(Path(tmp) / "rejected", MEMORY_CFG,
                                                       True, True, request=request)
            self.assertEqual(result.returncode, 3, result.stderr)
            self.assertFalse(receipt["configuration_accepted"])
            self.assertIsNotNone(receipt["error"])
            self.assertIsNone(captured)


if __name__ == "__main__":
    unittest.main()
