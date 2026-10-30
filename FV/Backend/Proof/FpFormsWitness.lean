import FV.Backend.Proof.RegallocCover

/-!
# S11e1 witnesses: the scalar FP data-movement forms

`fpuLoad`/`fpuStore` (`FpuLoad32/64`, `FpuStore32/64`), `fpuCSel` (`FpuCSel32/64`),
`fpuMoveFPImm` and `vecDupImm`: their ISLE decoding (`MInst.ofV`), their expansion into the
S11d `Insn`s (`MInst.lines`), the covered forms (`FormOk`), the values `ispec` gives them, and
concrete instances of the premises of `os_vecDupImm`/`linesOk_vecDupImm` and of the
`fpuLoad`/`fpuStore` coverage (`formOk_fpuLoad`/`formOk_fpuStore`).
-/

namespace Backend.Proof.FpFormsWitness

open Backend Backend.Proof Isle Isle.Aarch64

def ctx0 : FnCtx := { k := 0, slotBase := 16 }

/-- The instructions of an expansion (`none` on an expansion error). -/
def insns (m : MInst) : Option (List Insn) :=
  match MInst.lines ctx0 m {} with
  | .ok (ls, _) => some (ls.filterMap fun | .ins i _ => some i | _ => none)
  | .error _ => none

def fl0 : Clif.MemFlags := default
def r (k : Nat) : V := .reg (.v k)
def cEq : V := .data tyCond VIdx.Cond.Eq []
def s64 : V := .data tyScalarSize VIdx.ScalarSize.Size64 []
def v32x2 : V := .data tyVectorSize VIdx.VectorSize.Size32x2 []
def slot8 : V := .data tyAMode VIdx.AMode.SlotOffset [.int 8]

/-! ## `MInst.ofV` -/

example : MInst.ofV (.data tyMInst VIdx.MInst.FpuCSel64 [r 0, r 1, r 2, cEq]) =
    some (.fpuCSel .size64 (.v 0) (.v 1) (.v 2) .eq) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuCSel32 [r 0, r 1, r 2, cEq]) =
    some (.fpuCSel .size32 (.v 0) (.v 1) (.v 2) .eq) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuMoveFPImm
    [r 3, .op (.fpModImm ⟨0x70#8, .size64⟩), s64]) =
    some (.fpuMoveFPImm (.v 3) ⟨0x70#8, .size64⟩ .size64) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.VecDupImm
    [r 4, .op (.movModImm ⟨0#8, 0, false, false⟩), .bool false, v32x2]) =
    some (.vecDupImm (.v 4) ⟨0#8, 0, false, false⟩ false .size32x2) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuLoad64 [r 5, slot8, .op (.memFlags fl0)]) =
    some (.fpuLoad .size64 (.v 5) (.slotOffset 8) fl0) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuLoad32 [r 5, slot8, .op (.memFlags fl0)]) =
    some (.fpuLoad .size32 (.v 5) (.slotOffset 8) fl0) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuStore64 [r 6, slot8, .op (.memFlags fl0)]) =
    some (.fpuStore .size64 (.v 6) (.slotOffset 8) fl0) := by decide
example : MInst.ofV (.data tyMInst VIdx.MInst.FpuStore32 [r 6, slot8, .op (.memFlags fl0)]) =
    some (.fpuStore .size32 (.v 6) (.slotOffset 8) fl0) := by decide

/-! ## `MInst.lines` -/

example : insns (.fpuCSel .size64 (.v 0) (.v 1) (.v 2) .ge) =
    some [.fpuCSel .size64 (.v 0) (.v 1) (.v 2) .ge] := by decide
example : insns (.fpuMoveFPImm (.v 3) ⟨0x70#8, .size32⟩ .size32) =
    some [.fpuMoveFPImm .size32 (.v 3) 0x70] := by decide
example : insns (.vecDupImm (.v 4) ⟨0#8, 0, false, false⟩ false .size32x2) =
    some [.movi .size32x2 (.v 4) 0] := by decide
-- the inverted, shifted and 64-bit-mask forms are not expanded
example : insns (.vecDupImm (.v 4) ⟨0#8, 0, false, false⟩ true .size32x2) = none := by decide
example : insns (.vecDupImm (.v 4) ⟨1#8, 8, false, false⟩ false .size32x2) = none := by decide
example : insns (.vecDupImm (.v 4) ⟨0xff#8, 0, true, false⟩ false .size64x2) = none := by decide
-- a slot at `sp + 8 + 16`: `ldur`/`stur`; a slot beyond the `simm9` range: scaled `ldr`/`str`;
-- beyond the scaled range: the offset in `x16`
example : insns (.fpuLoad .size64 (.v 5) (.slotOffset 8) fl0) =
    some [.fpuLoad .size64 (.v 5) (.unscaled .sp 24)] := by decide
example : insns (.fpuStore .size32 (.v 6) (.slotOffset 1008) fl0) =
    some [.fpuStore .size32 (.v 6) (.unsignedOffset .sp 1024)] := by decide
example : (insns (.fpuLoad .size64 (.v 5) (.slotOffset 65536) fl0)).map List.getLast? =
    some (some (.fpuLoad .size64 (.v 5) (.regExtended .sp (.x 16) .sxtx))) := by decide

/-! ## `FormOk` -/

example : FormOk ctx0 (.fpuCSel .size64 (.vreg 0 .float) (.vreg 1 .float) (.vreg 2 .float) .eq) =
    true := rfl
example : FormOk ctx0 (.fpuMoveFPImm (.vreg 0 .float) ⟨0x70#8, .size64⟩ .size64) = true := rfl
example : FormOk ctx0 (.vecDupImm (.vreg 0 .float) ⟨0#8, 0, false, false⟩ false .size32x2) =
    true := rfl
-- an integer-class register, or an unexpanded `movi` form, is not covered
example : FormOk ctx0 (.fpuCSel .size64 (.vreg 0 .int) (.vreg 1 .float) (.vreg 2 .float) .eq) =
    false := rfl
example : FormOk ctx0 (.vecDupImm (.vreg 0 .float) ⟨0#8, 0, false, false⟩ true .size32x2) =
    false := rfl
-- the SIMD&FP loads/stores: a 32/64-bit size, a float data register, a covered mode
example : FormOk ctx0 (.fpuLoad .size64 (.vreg 0 .float) (.slotOffset 8) fl0) = true := rfl
example : FormOk ctx0 (.fpuStore .size32 (.vreg 0 .float)
    (.unsignedOffset (.vreg 1 .int) 1024) fl0) = true := rfl
example : FormOk ctx0 (.fpuLoad .size32 (.vreg 0 .float)
    (.regScaled (.vreg 1 .int) (.vreg 2 .int)) fl0) = true := rfl
example : FormOk ctx0 (.fpuLoad .size128 (.vreg 0 .float) (.slotOffset 8) fl0) = false := rfl
example : FormOk ctx0 (.fpuStore .size64 (.vreg 0 .int) (.slotOffset 8) fl0) = false := rfl
-- an unscaled offset outside `simm9`, an unaligned scaled offset
example : FormOk ctx0 (.fpuLoad .size64 (.vreg 0 .float) (.unscaled (.vreg 1 .int) 256) fl0) =
    false := by decide
example : FormOk ctx0 (.fpuStore .size64 (.vreg 0 .float)
    (.unsignedOffset (.vreg 1 .int) 12) fl0) = false := by decide

/-! ## Values -/

-- `fmov d, #1.0` (imm8 0x70) and `fmov s, #-0.125` (imm8 0xc0)
example : Arm.DPSFP.VFPExpandImm 11 52 0x70#8 = 0x3ff0000000000000#64 := by decide
example : Arm.DPSFP.VFPExpandImm 8 23 0xc0#8 = 0xbe000000#32 := by decide

example (w : Arm.ArmState) :
    ispec (.fpuMoveFPImm (.vreg 0 .float) ⟨0x70#8, .size64⟩ .size64) [] w =
      some ([(0x3ff0000000000000#64).setWidth 128], w, .next) := by
  simp only [ispec, defOut]
  congr 4

-- the zero of `f32const 0`/`f64const 0` (`movi vd.2s, #0`) and an all-ones `movi`
example : moviVal .size32x2 0#8 = 0#128 := moviVal_zero _
example : moviVal .size8x16 0xff#8 = BitVec.allOnes 128 := by decide
example : moviVal .size16x4 0xff#8 = 0x00ff00ff00ff00ff#128 := by decide

example (w : Arm.ArmState) :
    ispec (.vecDupImm (.vreg 0 .float) ⟨0#8, 0, false, false⟩ false .size32x2) [] w =
      some ([0#128], w, .next) := by
  simp [ispec, defOut, moviVal_zero]

/-! ## Premises of the `vecDupImm` lemmas -/

example (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.vecDupImm (.vreg 0 .float) ⟨0#8, 0, false, false⟩ false .size32x2) :=
  os_vecDupImm F ctx env X ⟨0#8, 0, false, false⟩ false .size32x2 0 rfl

example (ctx : FnCtx) : LinesOk ctx (.vecDupImm (.v 0) ⟨0#8, 0, false, false⟩ false .size32x2) :=
  linesOk_vecDupImm ctx _ _ false _ rfl

/-! ## The `fpuLoad`/`fpuStore` coverage -/

example (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuLoad .size64 (.vreg 0 .float) (.slotOffset 8) fl0) :=
  (formOk_fpuLoad (F := F) (X := X) (ctx := ctx) rfl).1 env

example (F : BitVec 64 → Prop) (ctx : FnCtx) (env : Env) (X : ExtSem) :
    OperandsSound F (execMInst ctx env) (csem F ctx X)
      (.fpuStore .size32 (.vreg 0 .float) (.regScaled (.vreg 1 .int) (.vreg 2 .int)) fl0) :=
  (formOk_fpuStore (F := F) (X := X) (ctx := ctx) rfl).1 env

example (ctx : FnCtx) : LinesOk ctx (.fpuLoad .size64 (.v 0) (.slotOffset 8) fl0) :=
  linesOk_fpuLoad ctx _ _ _ _ (fun _ h => AMode.noConfusion h)

end Backend.Proof.FpFormsWitness
