import FV.Backend.Asm
import FV.Backend.Encode
import FV.Backend.EmitOk
import FV.Backend.Isel

/-!
# `fcopysign`'s instructions: `FpuRRI` (`ushr`) and `FpuRRIMod` (`sli`)

Cranelift's scalar `fcopysign` (`inst.isle` `fcopy_sign`, rule 1) emits
`ushr vT.2s, vY.2s, #31; sli vX.2s, vT.2s, #31` at `f32` and `ushr dT, dY, #63; sli dX, dT, #63`
at `f64`. Witnesses: the extern constructors `fpu_op_ri_ushr`/`fpu_op_ri_sli` build the ISLE
values (`FPUOpRI.toV`/`FPUOpRIMod.toV`), `MInst.ofV` decodes them (out-of-range amounts and a lane
size other than the variant's do not decode), `MInst.lines` expands them (`sli` encodes `rd` and
`rn` only, as Cranelift's emitter does; the allocation ties `rd` to `ri`), the emission conditions
(`MInst.emitOk`), and the assembly text is Cranelift's disassembly (`floating-point.clif`
`%f31`/`%f32`).
-/

namespace Backend.FpuRRIData

open Backend Isle Isle.Aarch64

def ctx0 : FnCtx := { k := 0, slotBase := 16 }

/-- The instructions of an expansion (`none` on an expansion error). -/
def insns (m : MInst) : Option (List Insn) :=
  match MInst.lines ctx0 m {} with
  | .ok (ls, _) => some (ls.filterMap fun | .ins i _ => some i | _ => none)
  | .error _ => none

def r (k : Nat) : V := .reg (.v k)

/-! ## The extern constructors -/

example (ctx : Ctx) (st : LState) :
    externCtor ctx T.fpu_op_ri_ushr [.int 32, .int 31] st =
      .ok (FPUOpRI.toV (.uShr32 31), st) := rfl
example (ctx : Ctx) (st : LState) :
    externCtor ctx T.fpu_op_ri_ushr [.int 64, .int 63] st =
      .ok (FPUOpRI.toV (.uShr64 63), st) := rfl
example (ctx : Ctx) (st : LState) :
    externCtor ctx T.fpu_op_ri_sli [.int 32, .int 31] st =
      .ok (FPUOpRIMod.toV (.sli32 31), st) := rfl
example (ctx : Ctx) (st : LState) :
    externCtor ctx T.fpu_op_ri_sli [.int 64, .int 63] st =
      .ok (FPUOpRIMod.toV (.sli64 63), st) := rfl

/-! ## `MInst.ofV` -/

/-- `MInst.FpuRRI (UShr64 {amount 63, lane 64}) rd rn`. -/
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRI
    [.data tyFPUOpRI 1 [.int 63, .int 64], r 4, r 1]) =
    some (.fpuRRI (.uShr64 63) (.v 4) (.v 1)) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRI [FPUOpRI.toV (.uShr32 31), r 4, r 1]) =
    some (.fpuRRI (.uShr32 31) (.v 4) (.v 1)) := by decide
/-- `MInst.FpuRRIMod (Sli32 {amount 31, lane 32}) rd ri rn`. -/
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRIMod
    [.data tyFPUOpRIMod 0 [.int 31, .int 32], r 0, r 0, r 4]) =
    some (.fpuRRIMod (.sli32 31) (.v 0) (.v 0) (.v 4)) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRIMod [FPUOpRIMod.toV (.sli64 63), r 0, r 0, r 4]) =
    some (.fpuRRIMod (.sli64 63) (.v 0) (.v 0) (.v 4)) := by decide
-- out of range (`ushr #0`, `sli #32` at 32 bits) or the other variant's lane size: no decoding
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRI
    [.data tyFPUOpRI 0 [.int 0, .int 32], r 4, r 1]) = none := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRIMod
    [.data tyFPUOpRIMod 0 [.int 32, .int 32], r 0, r 0, r 4]) = none := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuRRI
    [.data tyFPUOpRI 0 [.int 63, .int 64], r 4, r 1]) = none := by decide

/-! ## Expansion, emission conditions, assembly text -/

example : insns (.fpuRRI (.uShr32 31) (.v 4) (.v 1)) = some [.fpuRRI (.uShr32 31) (.v 4) (.v 1)] := by
  decide
example : insns (.fpuRRIMod (.sli64 63) (.v 0) (.v 0) (.v 4)) =
    some [.fpuRRIMod (.sli64 63) (.v 0) (.v 4)] := by decide
-- `sli` encodes `rd` and `rn` only (`emit.rs`: `debug_assert_eq!(rd.to_reg(), ri)`, then `rd`'s
-- and `rn`'s register numbers; the allocation checker enforces the tie, as for `MovK`)
example : insns (.fpuRRIMod (.sli64 63) (.v 0) (.v 2) (.v 4)) =
    some [.fpuRRIMod (.sli64 63) (.v 0) (.v 4)] := by decide

example : (MInst.fpuRRI (.uShr64 64) (.v 4) (.v 1)).emitOk = true := by decide
example : (MInst.fpuRRI (.uShr32 33) (.v 4) (.v 1)).emitOk = false := by decide
example : (MInst.fpuRRIMod (.sli32 0) (.v 0) (.v 0) (.v 4)).emitOk = true := by decide
example : (MInst.fpuRRIMod (.sli64 64) (.v 0) (.v 0) (.v 4)).emitOk = false := by decide

example : (Insn.fpuRRI (.uShr32 31) (.v 4) (.v 1)).asm 0 = "ushr v4.2s, v1.2s, #0x1f" := by
  native_decide
example : (Insn.fpuRRIMod (.sli32 31) (.v 0) (.v 4)).asm 0 = "sli v0.2s, v4.2s, #0x1f" := by
  native_decide
example : (Insn.fpuRRI (.uShr64 63) (.v 4) (.v 1)).asm 0 = "ushr d4, d1, #0x3f" := by
  native_decide
example : (Insn.fpuRRIMod (.sli64 63) (.v 0) (.v 4)).asm 0 = "sli d0, d4, #0x3f" := by
  native_decide
example : (Insn.fpuRRI (.uShr64 1) (.v 4) (.v 1)).asm 0 = "ushr d4, d1, #1" := by native_decide

/-! ## Machine words: Cranelift's `emit_tests.rs` (`FpuRRI`, `FpuRRIMod`, `FpuRRRR`)

The test strings there are the little-endian bytes of the word (`"A204202F"` is `0x2f2004a2`). -/

/-- The word of one instruction (at pc 0, no labels). -/
def word (i : Insn) : Option (BitVec 32) := (i.encode { pc := 0, lbl := fun _ => none }).toOption

-- `ushr v2.2s, v5.2s, #32`, `ushr d2, d5, #63`
example : word (.fpuRRI (.uShr32 32) (.v 2) (.v 5)) = some 0x2f2004a2#32 := by native_decide
example : word (.fpuRRI (.uShr64 63) (.v 2) (.v 5)) = some 0x7f4104a2#32 := by native_decide
-- `sli v4.2s, v4.2s, v10.2s, #31`, `sli d4, d4, d10, #63` (`rd` = `ri` = `v4`)
example : word (.fpuRRIMod (.sli32 31) (.v 4) (.v 10)) = some 0x2f3f5544#32 := by native_decide
example : word (.fpuRRIMod (.sli64 63) (.v 4) (.v 10)) = some 0x7f7f5544#32 := by native_decide
-- `fmadd`/`fmsub s15, s30, s31, s1`, `fmadd`/`fmsub`/`fnmadd`/`fnmsub d15, d30, d31, d1`
example : word (.fpuRRRR .mAdd .size32 (.v 15) (.v 30) (.v 31) (.v 1)) = some 0x1f1f07cf#32 := by
  native_decide
example : word (.fpuRRRR .mSub .size32 (.v 15) (.v 30) (.v 31) (.v 1)) = some 0x1f1f87cf#32 := by
  native_decide
example : word (.fpuRRRR .mAdd .size64 (.v 15) (.v 30) (.v 31) (.v 1)) = some 0x1f5f07cf#32 := by
  native_decide
example : word (.fpuRRRR .mSub .size64 (.v 15) (.v 30) (.v 31) (.v 1)) = some 0x1f5f87cf#32 := by
  native_decide
example : word (.fpuRRRR .nMAdd .size64 (.v 15) (.v 30) (.v 31) (.v 1)) = some 0x1f7f07cf#32 := by
  native_decide
example : word (.fpuRRRR .nMSub .size64 (.v 15) (.v 30) (.v 31) (.v 1)) = some 0x1f7f87cf#32 := by
  native_decide
-- out of range: no word (`ushr #0`, `sli #32` at 32 bits)
example : word (.fpuRRI (.uShr32 0) (.v 2) (.v 5)) = none := by native_decide
example : word (.fpuRRIMod (.sli32 32) (.v 4) (.v 10)) = none := by native_decide

end Backend.FpuRRIData
