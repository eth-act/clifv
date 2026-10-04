# Upstream bugs found by this project

Bugs in pinned upstream components found by differential testing or proof work. Each entry has
a self-contained reproduction. Filing upstream is the owner's decision (public trackers). The fixes
are prepared as PRs on the owner's fork (`kevaundray/wasmtime`) for review first; nothing has
been reported to bytecodealliance yet.

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
  pass and Cranelift-native disagreeing on this run. Standalone copy:
  `corpus/upstream-bugs/cranelift-atomic-cas-i32.clif`.
- **Fix:** for I32, use the extended-register form with `uxtw` (`bit21 = 1`,
  `extend_op = 0b010000`), i.e. `cmp x27, w26, uxtw`. This is what the Lean backend emits
  (`FV/Backend/Asm.lean` `casLoopCmp`, a documented deviation from Cranelift).
- **PR (owner's fork, for review):** https://github.com/kevaundray/wasmtime/pull/1, branch
  `fix-aarch64-atomic-cas-i32`. Commit 1 adds a runtest and a precise-output test showing the
  bug (the runtest fails under qemu on aarch64); commit 2 is the fix.
- **Impact:** any `atomic_cas.i32` whose expected operand comes from a value with dirty upper
  bits. Rust code compiled with rustc_codegen_cranelift (`AtomicU32::compare_exchange`) can hit
  it when the expected value is produced by a truncation.

## Cranelift mid-end: `shifts.isle` (x << N) >> N rules build ill-typed IR for out-of-range N

- **Component:** Cranelift 0.136.1, `cranelift/codegen/src/opts/shifts.isle`, the two rules
  after the comment "(x << N) >> N == x as T_SMALL as T_LARGE" (lines 84 and 88: `sshr`/`ushr`
  of `ishl` by the same `iconst`).
- **Found by:** RulesRest (mid-end rule proofs: these two rules are the only ones found false
  under the CLIF semantics), 2026-10-03; reproduced with `clif2obj --opt-level speed`.
- **Bug:** the rules read the shift constant as a raw `u64` (`shift_u64`) and compute
  `u64_wrapping_sub (ty_bits ty) shift_u64` without masking the amount to the type width. CLIF
  shifts take the amount modulo the width, so `iconst.i64 -8` shifts an `i8` by 0. But
  `8 - 0xFFFF_FFFF_FFFF_FFF8` wraps to 16, so `shift_amt_to_type` gives `i16`, and the rule
  builds `sextend.i8 (ireduce.i16 x)` with `x : i8`. That is ill-typed (ireduce to a wider type,
  sextend to a narrower one). The original expression is just `x`.
- **Reproduction** (`corpus/upstream-bugs/cranelift-shifts-84-88.clif`):

  ```
  function %sshr_ishl_neg8(i8) -> i8 {
  block0(v0: i8):
      v1 = iconst.i64 -8
      v2 = ishl v0, v1
      v3 = sshr v2, v1
      return v3
  }
  ```

  `clif2obj --opt-level speed …` aborts: "inst7 (v8 = sextend.i8 v7): arg 0 (v7) with type i16
  failed to satisfy type set … 2 verifier errors detected. Compilation aborted." With
  `opt_level=none` it compiles and returns `x` (`clif-native`: all runs pass). With the verifier
  disabled, the ill-typed IR reaches lowering (not tried).
- **Fix:** mask the amount first (e.g. `shift_masked = shift_u64 & (ty_bits ty - 1)`, or require
  `u64_lt shift_u64 (ty_bits ty)` in an `if-let`), as the other shift rules do.
- **Effect here:** none. Neither rule is in the proven allow-list, and the Lean mid-end with all
  rules (`clif-opt`) doesn't apply it to the repro: the rewrite is dropped and the `ushr` variant
  folds to `v0`, which is correct.
