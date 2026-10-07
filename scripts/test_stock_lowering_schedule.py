"""Differential tests of the new schedule against the pinned, unchanged compiler.

These exercise the development harness. The production lowering checker/proof
cutover is a separate outstanding acceptance gate.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class StockScheduleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.trace = ROOT / ".lake/build/bin/lean-backend-lowering-trace"
        cls.compiler = ROOT / ".lake/build/bin/lean-stock-lowering-test"
        cls.exporter = ROOT / "tools/prejit-export/target/debug/prejit-export"
        cls.allocator = ROOT / "rust/target/release/lean-regalloc"
        if not all(p.exists() for p in (cls.trace, cls.compiler, cls.exporter, cls.allocator)):
            raise unittest.SkipTest("build the lowering trace, stock test harness, exporter and allocator")

    def compare(self, source, *, compile_bytes=True):
        with tempfile.TemporaryDirectory(prefix="stock-lowering_schedule-") as tmp:
            root = Path(tmp)
            path = root / "input.clif"
            path.write_text("test compile\nset opt_level=none\nset is_pic=false\n"
                            "set preserve_frame_pointers=false\ntarget aarch64\n\n" + source)
            stock = root / "stock"
            env = dict(os.environ, LEAN_REGALLOC=str(self.allocator))
            exported = subprocess.run(
                [self.exporter, path, stock, "aarch64-unknown-linux-gnu", "--all-stages"],
                cwd=ROOT, env=env, capture_output=True, text=True,
            )
            self.assertEqual(exported.returncode, 0, exported.stderr)
            manifest = json.loads((stock / "manifest.json").read_text())
            self.assertEqual(len(manifest["variants"]), 1, manifest)
            variant = manifest["variants"][0]
            self.assertEqual(variant["status"], "exported", variant)
            artifact = stock / "variant-0"
            assertions = json.loads((artifact / "assertions.json").read_text())
            self.assertTrue(all(row["passed"] for row in assertions), assertions)
            config = root / "config.json"
            config.write_text(json.dumps({"schema": 1, "target": variant["target"],
                                          "flags": variant["flags"], "isa_flags": variant["isa_flags"]}))
            reports = []
            for assertion in assertions:
                index = assertion["index"]
                input_path = artifact / f"{index}.lean.clif"
                report_path = root / f"{index}.trace.json"
                subprocess.run([self.trace, input_path, report_path], cwd=ROOT,
                               env=env, check=True, capture_output=True)
                report = json.loads(report_path.read_text())["functions"][0]["lowering"]["stock_schedule"]
                self.assertEqual(report["status"], "lowered", report)
                self.assertTrue(report["scan_replay"]["accepted"], report["scan_replay"])
                self.assertGreater(report["scan_replay"]["checked"], 0)
                block_replay = report["block_scan_replay"]
                self.assertTrue(block_replay["accepted"], block_replay)
                self.assertGreater(block_replay["checked"], 0)
                self.assertEqual(block_replay["records"], report["scan_replay"]["checked"])
                reports.append(report)
                # regalloc2's symbolic checker also validates native per-edge
                # argument requests, including cases the old adapter cannot express.
                request = root / f"{index}.allocator.json"
                request.write_text(json.dumps({"env": {
                    "preferred": [[f"x{i}" for i in range(16)],
                                  [f"v{i}" for i in [*range(8), *range(16, 32)]], []],
                    "non_preferred": [[f"x{i}" for i in [19, 20, 22, 23, 24, 25, 26, 27, 28, 21]],
                                      [f"v{i}" for i in range(8, 16)], []],
                    "scratch": [None, None, None], "fixed_stack": []},
                    "functions": [report["allocator_input"]]}))
                allocation = subprocess.run([self.allocator, request], cwd=ROOT,
                                            env=env, capture_output=True, text=True)
                self.assertEqual(allocation.returncode, 0, allocation.stderr)
                answer = json.loads(allocation.stdout)["functions"][0]
                self.assertEqual(answer.get("checker"), "ok", answer)
                if compile_bytes:
                    out = root / "lean" / str(index)
                    compiled = subprocess.run([self.compiler, input_path, out, config],
                                              cwd=ROOT, env=env, capture_output=True, text=True)
                    self.assertEqual(compiled.returncode, 0, compiled.stderr)
                    name = assertion["name"].removeprefix("%")
                    self.assertEqual((out / f"{name}.bin").read_bytes(),
                                     (artifact / f"{index}.bin").read_bytes(), source)
                    metadata = json.loads((artifact / f"{index}.json").read_text())
                    self.assertEqual(json.loads((out / f"{name}.relocs.json").read_text()),
                                     metadata["relocations"])
                    self.assertEqual(json.loads((out / f"{name}.traps.json").read_text()),
                                     metadata["traps"])
            return reports

    def test_dead_constants_and_comparisons(self):
        self.compare("""function %dead(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 99
    v2 = icmp eq v0, v1
    return v0
}
""")

    def test_extended_register_demands_its_computed_source(self):
        source = (ROOT / "scripts/fixtures/stock-extended-demand.clif").read_text()
        # The source of the extended ALU operand is a shift, not a parameter.
        # This checks replay, actual allocation and exact emitted stock bytes.
        self.compare(source)

    def test_fused_producers_and_sparse_value_ids(self):
        self.compare("""function %bic(i64, i64) -> i64 {
block0(v10: i64, v20: i64):
    v30 = bnot v20
    v40 = band v10, v30
    return v40
}
function %msub(i32, i32, i32) -> i32 {
block0(v0: i32, v1: i32, v2: i32):
    v3 = imul v1, v2
    v4 = isub v0, v3
    return v4
}
function %msub64(i64, i64, i64) -> i64 {
block0(v0: i64, v1: i64, v2: i64):
    v3 = imul v1, v2
    v4 = isub v0, v3
    return v4
}
""")

    def test_signed_address_and_compare_temporary_order(self):
        self.compare("""function %address(i32) -> i32 fast {
block0(v0: i32):
    v1 = sextend.i64 v0
    v2 = load.i32 v1
    return v2
}
function %compare(i64) -> i8 system_v {
block0(v0: i64):
    v2 = iconst.i64 0x4444444444444444
    v1 = icmp eq v0, v2
    return v1
}
""")

    def test_stack_address_fold(self):
        self.compare("""function %stack() -> i64 {
    ss0 = explicit_slot 8
block0:
    v0 = stack_addr.i64 ss0
    v1 = load.i64 notrap v0
    return v1
}
""")

    def test_load_sinking_and_memory_barriers(self):
        reports = self.compare("""function %sink(i64) -> i64 {
block0(v0: i64):
    v1 = load.i8 v0
    v2 = uextend.i64 v1
    return v2
}
function %barrier(i64, i8) -> i64 {
block0(v0: i64, v1: i8):
    v2 = load.i8 v0
    store v1, v0
    v3 = uextend.i64 v2
    return v3
}
function %unused_notrap(i64) -> i64 {
block0(v0: i64):
    v1 = load.i8 notrap v0
    return v0
}
function %unused_trapping(i64) -> i64 {
block0(v0: i64):
    v1 = load.i8 v0
    return v0
}
""")
        self.assertTrue(any(reports[0]["sunk"]))
        self.assertFalse(any(reports[1]["sunk"]))

    def test_transitive_multiple_uses_block_sinking(self):
        reports = self.compare("""function %multiple(i64) -> i64 {
block0(v0: i64):
    v1 = load.i8 v0
    v2 = uextend.i64 v1
    v3 = iadd v2, v2
    return v3
}
""")
        self.assertFalse(any(reports[0]["sunk"]))

    def test_atomic_load_extension_sinks_once(self):
        reports = self.compare("""function %atomic(i64) -> i64 {
block0(v0: i64):
    v1 = atomic_load.i8 v0
    v2 = uextend.i64 v1
    return v2
}
""")
        self.assertTrue(any(reports[0]["sunk"]))

    def test_implicit_sret_demand(self):
        self.compare("""function %sret(i64 sret) {
block0(v0: i64):
    return
}
""")

    def test_cross_block_demands(self):
        self.compare("""function %cross(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 17
    jump block1
block1:
    v2 = iadd v0, v1
    return v2
}
""")

    def test_multiple_call_results(self):
        self.compare("""function %pair() -> i64, i64 {
    sig0 = () -> i64, i64 system_v
    fn0 = colocated %external sig0
block0:
    v0, v1 = call fn0()
    return v0, v1
}
""")

    def test_loop_and_noncritical_branch_arguments(self):
        self.compare("""function %loop(i64) -> i64 {
block0(v0: i64):
    jump block1(v0)
block1(v1: i64):
    v2 = iconst.i64 1
    v3 = isub v1, v2
    brif v3, block1(v3), block2(v3)
block2(v4: i64):
    return v4
}
""", compile_bytes=False)

    def test_exception_return_payload_preallocation_and_aliases(self):
        self.compare("""function %exception(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %external sig0
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v1: i64):
    return v1
block2(v2: i64):
    return v2
}
""", compile_bytes=False)

    def test_exception_reservations_between_layout_value_allocations(self):
        reports = self.compare("""function %two_exceptions(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %external sig0
block0(v10: i64):
    try_call fn0(v10), sig0, block1(ret0), [ tag0: block3(exn0) ]
block1(v20: i64):
    try_call fn0(v20), sig0, block2(ret0), [ tag0: block3(exn0) ]
block2(v30: i64):
    return v30
block3(v40: i64):
    return v40
}
""", compile_bytes=False)
        for report in reports:
            self.assertEqual(report["initial_next_vreg"], 202)
            self.assertEqual(len(report["value_regs"]), 4)
            for value, register in zip(report["value_regs"], (192, 196, 200, 201)):
                self.assertIn(f"vreg {register} ", value["reg"])


if __name__ == "__main__":
    unittest.main()
