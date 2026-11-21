import FV.Backend.Proof.DeadCleanupSem

/-! Witnesses for #1141: the cleanup drops the dead `fcmp eq x, x` of cg_clif's NaN test before a
saturating float-to-integer conversion, because the conversion (`fcvtzu`/`fcvtzs`, `fpuToInt`) is
a flag-free producer and the `select` compares again. Cranelift never lowers that first `fcmp`:
the `select` rule looks through it (`isa/aarch64/lower.isle`). Shape: serde_json's
`lexical::num::as_u64` for `f64` (`_RNxC7lexical12H3AbvLnrpT90`, #1141):
`v3 = fcmp eq v0, v0; v2 = fcvt_to_uint_sat.i64 v0; v4 = iconst 0; v5 = select v3, v2, v4`.
Stock emits `fcvtzu; mov #0; fcmp; csel`.

Negative witnesses: the first `fcmp` stays when an instruction that reads the flags (`cset`) or
touches memory (a load) sits before the second compare, and a conversion whose result is used
stays. -/

namespace Backend.DeadCleanup
open Backend.Proof

private def nanTest : MInst := .fpuCmp .size64 (.vreg 0 .float) (.vreg 0 .float)
private def cvtU : MInst := .fpuToInt .f64ToU64 (.vreg 1 .int) (.vreg 0 .float)
private def cvtS : MInst := .fpuToInt .f64ToI64 (.vreg 1 .int) (.vreg 0 .float)
private def zero : MInst := .movWide .movZ (.vreg 2 .int) ⟨0, 0⟩ .size64
private def selEq : MInst := .csel (.vreg 3 .int) (.vreg 1 .int) (.vreg 2 .int) .eq
private def retSel : MInst := .rets [(.vreg 3 .int, .x 0)]
/-- the value of the conversion also returned: it stays live -/
private def retBoth : MInst := .rets [(.vreg 3 .int, .x 0), (.vreg 1 .int, .x 1)]
/-- reads the flags of the first `fcmp`: not flag-free -/
private def readFlags : MInst := .cset (.vreg 4 .int) .vs
private def retFlags : MInst := .rets [(.vreg 3 .int, .x 0), (.vreg 4 .int, .x 1)]
/-- a load between the compares: not a producer the cleanup steps over -/
private def load : MInst :=
  .load .uload64 (.vreg 4 .int) (.unsignedOffset (.vreg 5 .int) 0) default

/-- The conversions are flag-free producers. -/
example : pureForm cvtU = true ∧ flagFree cvtU = true ∧ flagFree cvtS = true := ⟨rfl, rfl, rfl⟩

/-- Their specification keeps the world and continues. -/
example (a : BitVec 128) (w : Arm.ArmState) : ∃ outs, mspec 0 cvtU [a] w = some (outs, w, .next) :=
  ⟨_, rfl⟩

/-- From a world whose flags a compare wrote they step alike (they read no flags). -/
example (a : BitVec 128) (p : Arm.PState) (w : Arm.ArmState) :
    mspec 0 cvtU [a] (Arm.write_pstate p w) =
      (mspec 0 cvtU [a] w).map (fun r => (r.1, Arm.write_pstate p r.2.1, r.2.2)) :=
  mspec_flagFree_pstate rfl p w

/-- The NaN test's dead `fcmp` goes: `fcvtzu; mov #0; fcmp; csel`, as stock emits. -/
example : (scan 6 [nanTest, cvtU, zero, nanTest, selEq, retSel] []).1 =
    [cvtU, zero, nanTest, selEq, retSel] := by decide

/-- The same with `fcvtzs`. -/
example : (scan 6 [nanTest, cvtS, zero, nanTest, selEq, retSel] []).1 =
    [cvtS, zero, nanTest, selEq, retSel] := by decide

/-- Negative: a `cset` reading the first `fcmp`'s flags keeps that `fcmp`. -/
example : (scan 6 [nanTest, cvtU, readFlags, zero, nanTest, selEq, retFlags] []).1 =
    [nanTest, cvtU, readFlags, zero, nanTest, selEq, retFlags] := by decide

/-- Negative: a load between the compares keeps the first `fcmp`. -/
example : (scan 6 [nanTest, cvtU, load, zero, nanTest, selEq, retSel] []).1 =
    [nanTest, cvtU, load, zero, nanTest, selEq, retSel] := by decide

/-- Negative: a conversion whose result is returned stays (only the dead `fcmp` goes). -/
example : (scan 6 [nanTest, cvtU, zero, nanTest, selEq, retBoth] []).1 =
    [cvtU, zero, nanTest, selEq, retBoth] := by decide

/-- The production pass (`prune`) on the whole function. -/
example : ∃ vc : VCode, (prune vc).blocks[0]!.insts.toList = [cvtU, zero, nanTest, selEq, retSel] := by
  refine ⟨⟨"as_u64", #[⟨0, #[nanTest, cvtU, zero, nanTest, selEq, retSel], #[], #[]⟩],
    #[.float, .int, .int, .int], 0, 0, #[], #[], none⟩, ?_⟩
  decide +kernel

end Backend.DeadCleanup
