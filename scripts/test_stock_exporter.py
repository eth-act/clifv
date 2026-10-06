"""Tests for exact pre-JIT comparison and stock-export integration."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import stock_common as BASELINE


class ComparisonTests(unittest.TestCase):
    def test_exact_match(self):
        self.assertTrue(BASELINE.comparison(b"abcd", b"abcd", [], [])["exact_code_and_relocations"])

    def test_instruction_change(self):
        self.assertFalse(BASELINE.comparison(b"abcd", b"abce", [], [])["exact_code_and_relocations"])

    def test_relocation_kind_target_addend_and_offset(self):
        relocation = {"offset":0,"kind":"Arm64Call","target":"foo","addend":0}
        for field, value in [("kind","Abs8"),("target","bar"),("addend",4),("offset",4)]:
            changed = {**relocation, field:value}
            self.assertFalse(BASELINE.comparison(b"abcd", b"abcd", [relocation], [changed])["exact_code_and_relocations"])

    def test_symbol_identity_not_byte_normalization(self):
        r = {"offset":0,"kind":"Arm64Call","target":"%foo","addend":0}
        self.assertTrue(BASELINE.comparison(b"abcd",b"abcd",[r],[{**r,"target":"foo"}])["exact_code_and_relocations"])
        self.assertFalse(BASELINE.comparison(b"abcd",b"abce",[r],[{**r,"target":"foo"}])["exact_code_and_relocations"])


class ExportIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.binary = BASELINE.ROOT / "tools/prejit-export/target/debug/prejit-export"
        if not cls.binary.exists():
            raise unittest.SkipTest("build the pinned exporter first")
        cls.stock = BASELINE.ROOT / "third_party/wasmtime/cranelift/filetests/filetests/runtests"

    def export(self, directory, file="alias.clif", target=BASELINE.TARGET, stock_load=False):
        argv = [str(self.binary),str(self.stock/file),str(directory),target]
        if stock_load: argv.append("--stock-load")
        subprocess.run(argv,check=True,capture_output=True)
        return json.loads((directory/"manifest.json").read_text())

    def test_compile_only_matches_stock_host_jit_compilation(self):
        host = subprocess.check_output(["rustc","-vV"],text=True).split("host: ")[1].splitlines()[0]
        with tempfile.TemporaryDirectory(prefix="prejit-test-") as temp:
            root = Path(temp)
            self.export(root/"export",target=host)
            self.export(root/"stock",target=host,stock_load=True)
            left, right = root/"export/variant-0",root/"stock/variant-0"
            for path in left.glob("*.bin"):
                self.assertEqual(path.read_bytes(),(right/path.name).read_bytes())
                a,b = json.loads(path.with_suffix(".json").read_text()),json.loads((right/path.with_suffix(".json").name).read_text())
                self.assertFalse(a.pop("jit_allocation_performed"))
                self.assertTrue(b.pop("jit_allocation_performed"))
                self.assertEqual(a,b)

    def test_no_jit_allocation_and_repeatability(self):
        with tempfile.TemporaryDirectory(prefix="prejit-test-") as temp:
            root = Path(temp)
            for file in ("alias.clif","call.clif","arithmetic.clif"):
                a,b = root/file/"a",root/file/"b"
                first = self.export(a,file)
                self.export(b,file)
                self.assertTrue(all(v["status"]=="exported" for v in first["variants"]))
                for path in a.rglob("*.bin"):
                    other = b/path.relative_to(a)
                    self.assertEqual(path.read_bytes(),other.read_bytes())
                for path in a.rglob("*.json"):
                    if path.name != "manifest.json":
                        self.assertFalse(json.loads(path.read_text())["jit_allocation_performed"])

    def test_signature_adaptation_is_exported_and_stock_checked(self):
        with tempfile.TemporaryDirectory(prefix="prejit-test-") as temp:
            root = Path(temp)
            manifest = self.export(root,"call.clif")
            self.assertTrue(all(v["status"]=="exported" for v in manifest["variants"]))
            adapted = root/"variant-0/1.lean.clif"
            self.assertIn("fn0 = %callee_i64 (i64)",adapted.read_text())
            self.assertIn("fn0 = %callee_i64 sig0",adapted.with_name("1.clif").read_text())

    def test_foreign_target_is_not_silently_retargeted(self):
        with tempfile.TemporaryDirectory(prefix="prejit-test-") as temp:
            manifest = self.export(Path(temp),"x64/fmsub.clif")
            self.assertEqual(manifest["variants"],[])

    def test_dynamic_vector_printer_limit_does_not_stop_reference_export(self):
        with tempfile.TemporaryDirectory(prefix="prejit-test-") as temp:
            manifest = self.export(Path(temp),"dynamic-simd-arithmetic.clif")
            self.assertTrue(all(v["status"]=="exported" for v in manifest["variants"]))


if __name__ == "__main__":
    unittest.main()
