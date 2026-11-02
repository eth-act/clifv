"""Fail-closed contract tests and integration with both actual stock stages."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("stock_compare",Path(__file__).with_name("stock-compiler-compare.py"))
COMPARE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COMPARE)


def with_flag(request, key, name, value):
    changed = copy.deepcopy(request)
    next(f for f in changed[key] if f["name"] == name)["value"] = value
    return changed


class ContractTests(unittest.TestCase):
    def test_extra_compiler_arguments_are_recorded_without_changing_request(self):
        variant = {"target": "aarch64", "flags": [], "isa_flags": [], "stage": "compile",
                   "isa_index": 0, "command_index": 0}
        def run(argv, directory, name, env):
            config = Path(argv[argv.index("--stock-config") + 1])
            receipt = Path(argv[argv.index("--config-receipt") + 1])
            receipt.write_text(json.dumps({"schema": 1, "request": json.loads(config.read_text()),
                                          "configuration_accepted": True, "function_rejections": {}}))
            return {"exit": 0, "argv": [str(arg) for arg in argv]}
        with tempfile.TemporaryDirectory() as tmp, patch.object(COMPARE, "command", run), \
                patch.object(COMPARE, "LEAN_COMPILER_ARGS", ["--no-dead-cleanup"]):
            _, contract = COMPARE.compile_lean(variant, b"input", Path(tmp) / "compile", {})
            self.assertIn("--no-dead-cleanup", contract["command"]["argv"])
            self.assertEqual(contract["request"], COMPARE.request_for(variant, b"input"))
            self.assertTrue(contract["contract_verified"])

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

    def test_function_rejections_must_be_a_name_to_reason_map(self):
        self.assertEqual(COMPARE.function_rejections({"function_rejections":{"f":"has_lse=true"}}),{"f":"has_lse=true"})
        for receipt in ({},{"function_rejections":None},{"function_rejections":["f"]},{"function_rejections":{"f":1}}):
            self.assertIsNone(COMPARE.function_rejections(receipt))

    def test_function_stock_signed_is_a_setting_gap(self):
        words = lambda *ws: b"".join(w.to_bytes(4, "little") for w in ws)
        signs = {"isa_flags":[{"name":"sign_return_address","value":"true"}]}
        unsigned = {"isa_flags":[{"name":"sign_return_address","value":"false"}]}
        # paciasp ... autiasp; ret, pacibsp ... retab, and an unsigned leaf.
        for code in (words(0xd503233f, 0xa9bf7bfd, 0xd50323bf, 0xd65f03c0), words(0xd503237f, 0xd65f0fff)):
            self.assertTrue(COMPARE.signing_gap(signs, code))
            self.assertFalse(COMPARE.signing_gap(unsigned, code))
        self.assertFalse(COMPARE.signing_gap(signs, words(0x8b010000, 0xd65f03c0)))
        signed = words(0xd503233f, 0xd50323bf, 0xd65f03c0)
        for status in ("identical_code_artifact", "different_code_artifact"):
            row = COMPARE.check_signing({"name":"%f","status":status}, signs, signed)
            self.assertEqual((row["status"], row["reason"]), ("unsupported_configuration", COMPARE.SIGNING_GAP))
        # Lean did not compile it: an operation gap, whatever stock does.
        uncompiled = {"name":"%f","status":"lean_unsupported","reason":"see lean.stderr and traps.json"}
        self.assertIs(COMPARE.check_signing(uncompiled, signs, signed), uncompiled)

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
            requests.append(with_flag(base,"isa_flags","use_bti","true"))
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
            self.assertIn("is_pic=false",receipt["function_rejections"]["far"])
            self.assertFalse((root/"far/dump/far.bin").exists())

    def test_settings_accepted_only_for_functions_they_cannot_change(self):
        source=(b"function %leaf(i64) -> i64 {\nblock0(v0: i64):\nreturn v0\n}\n\n"
                b"function %rmw_add(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n"
                b"v2 = atomic_rmw.i64 add v0, v1\nreturn v2\n}\n\n"
                b"function %rmw_xchg(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n"
                b"v2 = atomic_rmw.i64 xchg v0, v1\nreturn v2\n}\n\n"
                b"function %cas(i64, i64, i64) -> i64 {\nblock0(v0: i64, v1: i64, v2: i64):\n"
                b"v3 = atomic_cas.i64 v0, v1, v2\nreturn v3\n}\n\n"
                b"function %table(i32) -> i32 {\nblock0(v0: i32):\nbr_table v0, block1, [block2]\n"
                b"block1:\nv1 = iconst.i32 1\nreturn v1\nblock2:\nv2 = iconst.i32 2\nreturn v2\n}\n")
        names=("leaf","rmw_add","rmw_xchg","cas","table")
        with tempfile.TemporaryDirectory(prefix="stock-config-test-") as temp:
            root=Path(temp);base=self.seed(root/"stock")
            cases={
                # Accepted for every function Lean compiles.
                "inert":(with_flag(with_flag(with_flag(with_flag(base,"flags","enable_llvm_abi_extensions","true"),
                    "flags","enable_multi_ret_implicit_sret","true"),"isa_flags","has_fp16","true"),
                    "isa_flags","has_dotprod","true"),set()),
                "lse":(with_flag(base,"isa_flags","has_lse","true"),{"rmw_add","cas"}),
                "csdb":(with_flag(base,"isa_flags","use_csdb","true"),{"table"}),
                # The atomic loops save x24-x28, so those functions need a frame and are signed.
                "sign":(with_flag(with_flag(with_flag(base,"isa_flags","sign_return_address","true"),
                    "isa_flags","sign_return_address_with_bkey","true"),"isa_flags","has_pauth","true"),
                    {"rmw_add","rmw_xchg","cas"}),
            }
            for label,(request,rejected) in cases.items():
                result,receipt=self.compile(root/label,request,source)
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertTrue(receipt["configuration_accepted"],label)
                self.assertEqual(set(receipt["function_rejections"]),rejected,label)
                for name in names:
                    self.assertEqual((root/label/"dump"/f"{name}.bin").exists(),name not in rejected,(label,name))
            framed=with_flag(with_flag(base,"isa_flags","sign_return_address","true"),"flags","preserve_frame_pointers","true")
            signed_all=with_flag(with_flag(base,"isa_flags","sign_return_address","true"),"isa_flags","sign_return_address_all","true")
            for label,request in (("framed",framed),("signed-all",signed_all)):
                result,receipt=self.compile(root/label,request,source)
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertEqual(set(receipt["function_rejections"]),set(names),label)

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
            variant=COMPARE.one(COMPARE.SUITE/"isa/aarch64/bswap.clif",root,self.env,self.exporter,True)["variants"][0]
            stage=root/"files/isa/aarch64/bswap/stock/variant-0"
            meta=COMPARE.artifacts(stage,variant)[variant["functions"].index("%f0")]
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
            variant=COMPARE.one(COMPARE.SUITE/"runtests/call.clif",root,self.env,self.exporter,True)["variants"][0]
            stage=root/"files/runtests/call/stock/variant-0"
            meta=COMPARE.artifacts(stage,variant)[variant["functions"].index("%colocated_i64")]
            lean=root/"files/runtests/call/variant-0/compilation-0/lean"
            path=lean/"dump/colocated_i64.relocs.json"
            relocs=json.loads(path.read_text());relocs[0]["addend"]=4
            path.write_text(json.dumps(relocs))
            changed=copy.deepcopy(meta[1]);changed["relocations"][0]["addend"]=4
            compared=COMPARE.compare_function("%colocated_i64",(meta[0],changed),lean,True,True)
            self.assertTrue(compared["exact_code_and_relocations"])
            self.assertFalse(compared["lean_dump_matches_object_relocations"])
            self.assertFalse(compared["exact_code_artifact"])

    def test_repeated_function_names_are_compared_separately(self):
        # shift-op.clif has two compile-test functions named %f, of different types.
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            root=Path(temp)
            variant=COMPARE.one(COMPARE.SUITE/"isa/aarch64/shift-op.clif",root,self.env,self.exporter,True)["variants"][0]
            self.assertEqual(variant["functions"],["%f","%f"])
            stage=root/"files/isa/aarch64/shift-op/stock/variant-0"
            metas=COMPARE.artifacts(stage,variant)
            self.assertEqual(sorted(metas),[0,1])
            self.assertNotEqual((stage/"0.bin").read_bytes(),(stage/"1.bin").read_bytes())
            self.assertEqual([r["index"] for r in variant["functions_compared"]],[0,1])
            self.assertEqual([c["functions"] for c in variant["lean_compilations"]],[["%f"],["%f"]])
            inputs=[(root/f"files/isa/aarch64/shift-op/variant-0/compilation-{i}/input.clif").read_text() for i in (0,1)]
            self.assertIn("%f(i64) -> i64",inputs[0])
            self.assertIn("%f(i32) -> i32",inputs[1])
            # Each function is compared with its own stock artifact.
            rows=variant["functions_compared"]
            for k, r in enumerate(rows):
                self.assertEqual(r["bytes"]["left_sha256"],COMPARE.digest((stage/f"{k}.bin").read_bytes()))
            self.assertNotEqual(rows[0]["bytes"]["left_sha256"],rows[1]["bytes"]["left_sha256"])
            self.assertNotEqual(rows[0]["bytes"]["right_sha256"],rows[1]["bytes"]["right_sha256"])

    def test_exporter_names_compile_artifacts_by_position(self):
        with tempfile.TemporaryDirectory(prefix="stock-compare-test-") as temp:
            root=Path(temp)
            source=root/"repeated.clif"
            source.write_text("test compile\ntarget aarch64\n"
                "function %f() -> i64 {\nblock0:\nv0 = iconst.i64 1\nreturn v0\n}\n"
                "function %f() -> i64 {\nblock0:\nv0 = iconst.i64 2\nreturn v0\n}\n")
            subprocess.run([self.exporter,source,root/"out",COMPARE.TARGET,"--all-stages"],check=True,capture_output=True)
            stage=root/"out/variant-0"
            self.assertEqual([json.loads((stage/f"{k}.json").read_text())["index"] for k in (0,1)],[0,1])
            self.assertNotEqual((stage/"0.bin").read_bytes(),(stage/"1.bin").read_bytes())
            self.assertEqual([a["index"] for a in json.loads((stage/"assertions.json").read_text())],[0,1])
            variant=json.loads((root/"out/manifest.json").read_text())["variants"][0]
            self.assertEqual(sorted(COMPARE.artifacts(stage,variant)),[0,1])
            # A file stem that disagrees with the recorded position is not accepted.
            (stage/"1.json").rename(stage/"7.json")
            with self.assertRaises(ValueError):
                COMPARE.artifacts(stage,variant)

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


class StockDevelopmentIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler = COMPARE.ROOT / ".lake/build/bin/lean-stock-lowering-compare"
        cls.exporter = COMPARE.ROOT / "tools/prejit-export/target/debug/prejit-export"
        if not cls.compiler.exists() or not cls.exporter.exists():
            raise unittest.SkipTest("build the development comparison compiler and exporter")
        cls.env = dict(os.environ, LEAN_REGALLOC=str(COMPARE.ROOT / "rust/target/release/lean-regalloc"))

    def seed(self, root):
        subprocess.run([self.exporter, COMPARE.SUITE / "runtests/alias.clif", root / "stock",
                        COMPARE.TARGET, "--all-stages"], check=True, capture_output=True)
        return json.loads((root / "stock/manifest.json").read_text())["variants"][0]

    def test_mixed_supported_and_unsupported_functions_keep_exact_receipt_and_object(self):
        source = (b"function %good(i64) -> i64 {\nblock0(v0: i64):\nreturn v0\n}\n"
                  b"function %bad(f32) -> f32 {\nblock0(v0: f32):\nreturn v0\n}\n")
        with tempfile.TemporaryDirectory(prefix="stock-lowering_comparison-test-") as tmp:
            root = Path(tmp)
            variant = self.seed(root)
            with patch.object(COMPARE, "LEAN_BINARY", self.compiler):
                lean, contract = COMPARE.compile_lean(variant, source, root / "compilation", self.env)
            self.assertTrue(contract["contract_verified"], contract)
            self.assertEqual(contract["command"]["argv"][0], str(self.compiler))
            self.assertEqual(contract["request"]["input_sha256"], COMPARE.digest(source))
            self.assertTrue((lean / "dump/good.bin").exists())
            self.assertFalse((lean / "dump/bad.bin").exists())
            _, code = COMPARE.ELF(lean / "program.o").function("good")
            self.assertEqual(code, (lean / "dump/good.bin").read_bytes())
            diagnostics = (root / "compilation/lean.stderr").read_text()
            self.assertIn("unsupported", diagnostics)
            self.assertIn("%good: compiled, unverified:", diagnostics)

    def test_repeated_names_retain_compilation_occurrence_indices(self):
        with tempfile.TemporaryDirectory(prefix="stock-lowering_occurrence-test-") as tmp:
            with patch.object(COMPARE, "LEAN_BINARY", self.compiler):
                report = COMPARE.one(COMPARE.SUITE / "isa/aarch64/iabs.clif", Path(tmp),
                                     self.env, self.exporter, True)
            variant = report["variants"][0]
            repeated = [c for c in variant["lean_compilations"] if c["functions"] == ["%f11"]]
            self.assertEqual([c["function_indices"] for c in repeated], [[10], [11]])
            self.assertNotEqual(repeated[0]["request"]["input_sha256"],
                                repeated[1]["request"]["input_sha256"])

    def test_development_compiler_rejects_unsupported_settings_with_receipt(self):
        with tempfile.TemporaryDirectory(prefix="stock-lowering_comparison-test-") as tmp:
            root = Path(tmp)
            variant = copy.deepcopy(self.seed(root))
            next(f for f in variant["flags"] if f["name"] == "opt_level")["value"] = "speed"
            with patch.object(COMPARE, "LEAN_BINARY", self.compiler):
                lean, contract = COMPARE.compile_lean(variant, b"", root / "compilation", self.env)
            self.assertFalse(contract["contract_verified"])
            self.assertEqual(contract["command"]["exit"], 3)
            self.assertEqual(contract["receipt"]["request"], contract["request"])
            self.assertFalse(contract["receipt"]["configuration_accepted"])
            self.assertFalse((lean / "program.o").exists())

    def test_extended_demand_recovers_all_twenty_allocator_failures(self):
        investigation = json.loads((COMPARE.ROOT /
            "scripts/fixtures/stock-extended-demand.json").read_text())
        cases = investigation["allocator_cases"]
        self.assertEqual(len(cases), 20)
        with tempfile.TemporaryDirectory(prefix="stock-lowering_demand-regression-") as tmp:
            reports = {}
            with patch.object(COMPARE, "LEAN_BINARY", self.compiler):
                for source in sorted({c["test"] for c in cases}):
                    reports[source] = COMPARE.one(COMPARE.SUITE / source,
                        Path(tmp), self.env, self.exporter, True)
            for case in cases:
                with self.subTest(source=case["test"], variant=case["variant"],
                                  index=case["index"], name=case["name"]):
                    variant = next(v for v in reports[case["test"]]["variants"]
                                   if v["index"] == case["variant"])
                    function = next(f for f in variant["functions_compared"]
                                    if f["index"] == case["index"])
                    self.assertEqual(function["name"], case["name"])
                    self.assertIn(function["status"],
                                  ("identical_code_artifact", "different_code_artifact"))
                    self.assertTrue(function["settings_contract_verified"])
                    self.assertTrue(function["lean_dump_matches_object_bytes"])
                    self.assertTrue(function["lean_dump_matches_object_relocations"])


if __name__ == "__main__":
    unittest.main()
