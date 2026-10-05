"""Fail-closed contract tests and integration with both actual stock stages."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("stock_compare",Path(__file__).with_name("stock-compiler-compare.py"))
COMPARE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COMPARE)


class ContractTests(unittest.TestCase):
    def test_receipt_requires_exact_settings_and_input(self):
        request = {"schema":1,"input_sha256":COMPARE.digest(b"input"),"flags":[]}
        receipt = {"schema":1,"request":copy.deepcopy(request),"configuration_accepted":True}
        self.assertIsNone(COMPARE.verify_receipt(request,receipt,b"input"))
        self.assertIsNotNone(COMPARE.verify_receipt(request,receipt,b"changed"))
        receipt["request"]["flags"] = [{"name":"is_pic","value":"true"}]
        self.assertIsNotNone(COMPARE.verify_receipt(request,receipt,b"input"))

    def test_unsupported_or_missing_receipt_never_passes(self):
        request = {"schema":1,"input_sha256":COMPARE.digest(b"input")}
        for receipt in ({},{"schema":1,"request":request,"configuration_accepted":False,"error":"unsupported"}):
            self.assertIsNotNone(COMPARE.verify_receipt(request,receipt,b"input"))

    def test_all_encoder_relocation_types_are_known(self):
        self.assertEqual(COMPARE.ELF_RELOC_TYPES["Aarch64AdrGotPage21"],311)
        self.assertEqual(len(COMPARE.ELF_RELOC_TYPES),9)


class StockIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exporter = COMPARE.ROOT / "tools/prejit-export/target/debug/prejit-export"
        cls.lean = COMPARE.ROOT / ".lake/build/bin/lean-backend"
        if not cls.exporter.exists() or not cls.lean.exists():
            raise unittest.SkipTest("build the exporter and Lean backend first")
        cls.env = os.environ.copy()
        cls.env["PATH"] = str(COMPARE.ROOT / "rust/target/release") + os.pathsep + cls.env["PATH"]

    def export(self, file, directory):
        subprocess.run([self.exporter,COMPARE.SUITE/file,directory,COMPARE.TARGET,"--all-stages"],
            check=True,capture_output=True,env=self.env)
        return json.loads((directory/"manifest.json").read_text())

    def compile(self, directory, request, source=b"function %leaf(i64) -> i64 {\nblock0(v0: i64):\nreturn v0\n}\n", extra=()):
        directory.mkdir(parents=True)
        input_path, config, receipt = directory/"input.clif",directory/"config.json",directory/"receipt.json"
        input_path.write_bytes(source)
        config.write_text(json.dumps(request))
        result = subprocess.run([self.lean,input_path,directory/"program.o","--stock-config",config,
            "--config-receipt",receipt,"--dump",directory/"dump",*extra],capture_output=True,env=self.env)
        return result,json.loads(receipt.read_text()) if receipt.exists() else None

    def seed(self, directory):
        manifest = self.export("runtests/alias.clif",directory)
        return COMPARE.request_for(manifest["variants"][0],b"")

    def test_settings_are_honored_not_masked(self):
        with tempfile.TemporaryDirectory(prefix="stock-config-test-") as temp:
            root = Path(temp)
            base = self.seed(root/"stock")
            result, receipt = self.compile(root/"leaf",base)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertTrue(receipt["configuration_accepted"])
            self.assertEqual((root/"leaf/dump/leaf.bin").read_bytes(),bytes.fromhex("c0035fd6"))
            self.assertFalse(any(s["name"]==".eh_frame" for s in COMPARE.ELF(root/"leaf/program.o").sections))
            frame = copy.deepcopy(base)
            for flag in frame["flags"]:
                if flag["name"] in ("preserve_frame_pointers","unwind_info"): flag["value"]="true"
            result, receipt = self.compile(root/"frame",frame)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(receipt["request"],frame)
            self.assertGreater(len((root/"frame/dump/leaf.bin").read_bytes()),4)
            self.assertTrue(any(s["name"]==".eh_frame" for s in COMPARE.ELF(root/"frame/program.o").sections))

    def test_unknown_missing_duplicate_and_unimplemented_flags_rejected(self):
        with tempfile.TemporaryDirectory(prefix="stock-config-test-") as temp:
            root = Path(temp)
            base = self.seed(root/"stock")
            requests = []
            unknown = copy.deepcopy(base); unknown["flags"].append({"name":"future_feature","value":"true"});requests.append(unknown)
            missing = copy.deepcopy(base);missing["flags"].pop();requests.append(missing)
            duplicate = copy.deepcopy(base);duplicate["flags"].append(duplicate["flags"][0]);requests.append(duplicate)
            for name, value in (("opt_level","speed"),("enable_nan_canonicalization","true"),("enable_probestack","true")):
                request = copy.deepcopy(base)
                next(f for f in request["flags"] if f["name"]==name)["value"]=value
                requests.append(request)
            isa = copy.deepcopy(base);isa["isa_flags"][0]["value"]="true";requests.append(isa)
            for index, request in enumerate(requests):
                result, receipt = self.compile(root/f"case-{index}",request)
                self.assertEqual(result.returncode,3,result.stderr)
                self.assertFalse(receipt["configuration_accepted"])
                self.assertFalse((root/f"case-{index}/program.o").exists())

    def test_conflicting_driver_options_rejected_before_acceptance(self):
        with tempfile.TemporaryDirectory(prefix="stock-config-test-") as temp:
            root=Path(temp);base=self.seed(root/"stock")
            result,receipt=self.compile(root/"override",base,extra=("--opt",))
            self.assertEqual(result.returncode,2)
            self.assertIsNone(receipt)

    def test_non_pic_far_symbol_is_explicit_function_gap(self):
        with tempfile.TemporaryDirectory(prefix="stock-config-test-") as temp:
            root=Path(temp);base=self.seed(root/"stock")
            source=b"function %far() -> i64 {\nfn0 = %external () -> i64\nblock0:\nv0 = call fn0()\nreturn v0\n}\n"
            result,receipt=self.compile(root/"far",base,source)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertTrue(receipt["configuration_accepted"])
            self.assertIn(b"is_pic=false",result.stderr)
            self.assertFalse((root/"far/dump/far.bin").exists())

    def test_stock_compile_assertions_and_exact_outputs(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            row=COMPARE.one(COMPARE.SUITE/"isa/aarch64/bswap.clif",Path(temp),self.env,self.exporter,True)
            self.assertTrue(row["all_declared_aarch64_code_artifacts_identical"])
            variant=row["variants"][0]
            self.assertEqual(variant["stage"],"compile")
            self.assertEqual(variant["requested_target"],variant["target"])
            self.assertTrue(all(a["passed"] for a in variant["stock_compile_assertions"]))
            self.assertEqual(len(variant["functions_compared"]),3)
            self.assertTrue(all(r["lean_dump_matches_object_relocations"] for r in variant["functions_compared"]))
            self.assertFalse(any(r["full_artifact_equivalence_verified"] for r in variant["functions_compared"]))

    def test_stock_run_preparation_and_exact_outputs(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            row=COMPARE.one(COMPARE.SUITE/"runtests/alias.clif",Path(temp),self.env,self.exporter,True)
            self.assertTrue(row["all_declared_aarch64_code_artifacts_identical"])
            self.assertEqual(row["variants"][0]["stage"],"run")
            self.assertFalse(row["variants"][0]["stock_runtime_assertions_executed"])
            self.assertTrue(row["variants"][0]["reference_repeat_verified"])

    def test_metadata_mutation_and_nonrepeatability_cannot_pass(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            root=Path(temp)
            COMPARE.one(COMPARE.SUITE/"isa/aarch64/bswap.clif",root,self.env,self.exporter,True)
            stage=root/"files/isa/aarch64/bswap/stock/variant-0"
            meta=COMPARE.artifacts(stage)["%f0"]
            lean=root/"files/isa/aarch64/bswap/variant-0/compilation-0/lean"
            self.assertTrue(COMPARE.compare_function("%f0",meta,lean,True,True)["exact_code_artifact"])
            self.assertFalse(COMPARE.compare_function("%f0",meta,lean,True,False)["exact_code_artifact"])
            self.assertFalse(COMPARE.compare_function("%f0",meta,lean,False,True)["exact_code_artifact"])
            changed=copy.deepcopy(meta[1]);changed["alignment"]=8
            self.assertFalse(COMPARE.compare_function("%f0",(meta[0],changed),lean,True,True)["exact_code_artifact"])
            changed=copy.deepcopy(meta[1]);changed["traps"]=[{"offset":0,"code":"user1"}]
            self.assertFalse(COMPARE.compare_function("%f0",(meta[0],changed),lean,True,True)["exact_code_artifact"])

    def test_relocation_dump_disagreement_with_object_cannot_pass(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            root=Path(temp)
            COMPARE.one(COMPARE.SUITE/"runtests/call.clif",root,self.env,self.exporter,True)
            stage=root/"files/runtests/call/stock/variant-0"
            meta=COMPARE.artifacts(stage)["%colocated_i64"]
            lean=root/"files/runtests/call/variant-0/compilation-0/lean"
            path=lean/"dump/colocated_i64.relocs.json"
            relocs=json.loads(path.read_text());relocs[0]["addend"]=4
            path.write_text(json.dumps(relocs))
            changed=copy.deepcopy(meta[1]);changed["relocations"][0]["addend"]=4
            compared=COMPARE.compare_function("%colocated_i64",(meta[0],changed),lean,True,True)
            self.assertTrue(compared["exact_code_and_relocations"])
            self.assertFalse(compared["lean_dump_matches_object_relocations"])
            self.assertFalse(compared["exact_code_artifact"])

    def test_non_binary_and_foreign_files_remain_inventory_gaps(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            root=Path(temp)
            non_binary=COMPARE.one(COMPARE.SUITE/"parser/tiny.clif",root,self.env,self.exporter,True)
            self.assertEqual(non_binary["status"],"non_binary_test")
            foreign=COMPARE.one(COMPARE.SUITE/"runtests/x64/fmsub.clif",root,self.env,self.exporter,True)
            self.assertEqual(foreign["status"],"no_lean_target")
            self.assertTrue(foreign["manifest"]["declared_targets"])

    def test_no_default_isa_invented(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            root=Path(temp)
            source=root/"missing-isa.clif"
            source.write_text("test compile\nfunction %f() {\nblock0:\nreturn\n}\n")
            subprocess.run([self.exporter,source,root/"out",COMPARE.TARGET,"--all-stages"],check=True,capture_output=True)
            manifest=json.loads((root/"out/manifest.json").read_text())
            self.assertTrue(manifest["missing_required_isa"])
            self.assertEqual(manifest["variants"],[])


if __name__ == "__main__":
    unittest.main()
