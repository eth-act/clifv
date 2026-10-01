# Upstream bugs found by this project

Bugs in pinned upstream components found by differential testing or proof work. Each entry has
a self-contained reproduction and is ready to be filed. Filing is the owner's decision (public
trackers), so nothing below has been reported upstream yet.

## Cranelift aarch64: `atomic_cas.i32` compares all 64 bits of the expected value

- **Component:** Cranelift 0.136.1 (wasmtime v49.0.1, commit 46c23a8), aarch64 backend,
  `cranelift/codegen/src/isa/aarch64/inst/emit.rs`, `Inst::AtomicCASLoop` (around line 1747).
- **Found by:** AtomicsProof (proof of the LL/SC loop against the Arm model), 2026-10-01;
  reproduced with `clif-native` (Cranelift-native code under qemu).
- **Bug:** for `ty = I32`, the loop compares `cmp x27, x26`, the 64-bit form with no extend. The
  comment says "The top 32-bits are zero-extended by the ldaxr so we don't have to use UXTW",
  which holds for x27, the loaded value. It doesn't hold for x26, the expected value: an `i32` in
  a 64-bit register has unspecified upper bits in Cranelift's aarch64 backend (e.g. the result
  of `ireduce.i32` of an `i64` is the same register). If those bits are nonzero, the comparison
  fails although the low 32 bits match, the exchange isn't performed, and the old value is
  returned. The CLIF semantics (and the Cranelift interpreter) perform the exchange. I8/I16 use
  `uxtb`/`uxth` and are correct.
- **Reproduction** (`corpus/clif-regress/atomics_loops.clif`, function `%cas32`):

  ```
  function %cas32(i64, i32, i32) -> i32, i32 {
      ss0 = explicit_slot 8
  block0(v0: i64, v1: i32, v2: i32):
      v3 = stack_addr.i64 ss0
      store.i32 v1, v3
      v4 = ireduce.i32 v0
      v5 = atomic_cas.i32 v3, v4, v2
      v6 = load.i32 v3
      return v5, v6
  }
  ; run: %cas32(0x100000005, 5, 7) == [5, 7]
  ```

  Cranelift-native returns `[5, 5]`: memory unchanged. Expected: `[5, 7]`.
  `scripts/lean-backend-filetests.sh -v corpus/clif-regress/atomics_loops.clif` shows Lean 11/11
  pass and Cranelift-native disagreeing on this run.
- **Fix:** for I32, use the extended-register form with `uxtw` (`bit21 = 1`,
  `extend_op = 0b010000`), i.e. `cmp x27, w26, uxtw`. This is what the Lean backend emits
  (`FV/Backend/Asm.lean` `casLoopCmp`, a documented deviation from Cranelift).
- **Impact:** any `atomic_cas.i32` whose expected operand comes from a value with dirty upper
  bits. Rust code compiled with rustc_codegen_cranelift (`AtomicU32::compare_exchange`) can hit
  it when the expected value is produced by a truncation.
