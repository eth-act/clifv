#!/usr/bin/env python3
"""Run emitted bytes for distinct selected vectors and the checked spill fallback."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
NAMES = ("indexed_branch", "indexed_critical", "indexed_pair")
RUNNER = r"""
extern unsigned long indexed_branch(unsigned long, unsigned long);
extern unsigned char indexed_critical(unsigned long);
extern unsigned long indexed_pair(unsigned long, unsigned long, unsigned long);
static int check(void) {
  unsigned long values[] = {0, 1, 2, 255, 256, 0x8000000000000000UL, ~0UL};
  for (unsigned i = 0; i < 7; ++i) {
    unsigned long a = values[i];
    if (indexed_critical(a) != (unsigned char)a) return 1;
    for (unsigned j = 0; j < 7; ++j) {
      unsigned long b = values[j];
      if (indexed_branch(a, b) != (a ? b : a)) return 2;
      for (unsigned k = 0; k < 7; ++k) {
        unsigned long c = values[k];
        if (indexed_pair(a, b, c) != (a ? b-c : c-b)) return 3;
      }
    }
  }
  return 0;
}
void _start(void) {
  register long result __asm__("x0") = check();
  __asm__ volatile("mov x8, #93\nsvc #0" : : "r"(result) : "x8", "memory");
  __builtin_unreachable();
}
"""


class PerSuccessorAllocation(unittest.TestCase):
    def test_selected_vectors_and_both_allocations_execute(self):
        qemu = os.environ.get("CLIF_NATIVE_QEMU") or shutil.which("qemu-aarch64-static")
        clang = shutil.which("clang")
        toolchains = Path.home() / ".rustup/toolchains"
        llds = sorted(toolchains.glob("*/lib/rustlib/*/bin/rust-lld"))
        self.assertTrue(qemu and Path(qemu).is_file(), "set CLIF_NATIVE_QEMU")
        self.assertTrue(clang and llds, "clang and Rust's bundled linker required")
        compiler = ROOT / ".lake/build/bin/lean-stock-lowering-test"
        oracle = ROOT / "rust/target/release/lean-regalloc"
        self.assertTrue(compiler.is_file() and oracle.is_file(), "build the Stock harness and allocator first")
        with tempfile.TemporaryDirectory(prefix="clifv-per-edge-") as directory:
            work = Path(directory)
            runner = work / "runner.c"
            runner.write_text(RUNNER)
            subprocess.run([clang, "--target=aarch64-linux-gnu", "-ffreestanding", "-fno-builtin",
                            "-fno-stack-protector", "-fno-pic", "-nostdlib", "-O1", "-c",
                            str(runner), "-o", str(work / "runner.o")], check=True, capture_output=True)
            for mode in ("oracle", "fallback"):
                with self.subTest(mode=mode):
                    output = work / mode
                    request = work / "request.json"
                    env = dict(os.environ, LEAN_REGALLOC=str(oracle if mode == "oracle" else work / "absent-oracle"),
                               LEAN_REGALLOC_KEEP=str(request))
                    subprocess.run([str(compiler), str(ROOT / "scripts/fixtures/stock-per-edge-allocation.clif"),
                                    str(output)], env=env, cwd=ROOT, check=True, capture_output=True)
                    if mode == "oracle":
                        funcs = {f["name"]: f for f in json.loads(request.read_text())["functions"]}
                        branch = lambda name: next(i["args"] for i in funcs[name]["insts"] if i["kind"] == "branch")
                        self.assertEqual(branch("indexed_branch"), [[193], [192]])
                        self.assertEqual(branch("indexed_pair"), [[193, 194], [194, 193]])
                        self.assertEqual(branch("indexed_critical"), [[], []])
                    assembly = work / (mode + ".s")
                    assembly.write_text(".text\n" + "\n".join(
                        f'.globl {name}\n.type {name}, %function\n.p2align 2\n{name}:\n'
                        f'.incbin "{output / (name + ".bin")}"\n.size {name}, . - {name}\n'
                        for name in NAMES))
                    subprocess.run([clang, "--target=aarch64-linux-gnu", "-c", str(assembly), "-o",
                                    str(work / (mode + ".o"))], check=True, capture_output=True)
                    executable = work / (mode + ".elf")
                    subprocess.run([str(llds[0]), "-flavor", "gnu", "-m", "aarch64elf", "-static",
                                    "-e", "_start", str(work / "runner.o"), str(work / (mode + ".o")),
                                    "-o", str(executable)], check=True, capture_output=True)
                    executed = subprocess.run([str(qemu), str(executable)], capture_output=True, timeout=30)
                    self.assertEqual(executed.returncode, 0, executed.stderr.decode(errors="replace"))


if __name__ == "__main__":
    unittest.main()
