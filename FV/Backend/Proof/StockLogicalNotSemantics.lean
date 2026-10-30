import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamALUALogicNot

namespace Backend.Stock.Proof.LogicalNot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]

/-- Actual mapped/final-alias register NOT operations preserve all other registers. -/
theorem stock_not_rrr_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp}
    (operation : NotOp op)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x y nx ny d : Nat}
    (bounded : aliases.size ≤ d)
    (mappedX : ctx.valueReg? x = some (.vreg nx .int))
    (mappedY : ctx.valueReg? y = some (.vreg ny .int))
    (held : ValuesHeld (fun z => z = x ∨ z = y) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRR op (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int)).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty, notOpVal op u v⟩ (ρ' d) ∧
      ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have yValue := held.read (Or.inr rfl) (getAs_ok sourceY) mappedY
  obtain ⟨r, computed, value⟩ := aluVal_holds_not operation (szOf_bits width) xValue (opnd_setWidth_eq (szOf_bits width) yValue)
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have destination : Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int) =
      .vreg d .int := by
    rw [resolve_vreg]
    change Reg.vreg (aliasNum aliases d) .int = _
    rw [fresh]
  have code : (MInst.aluRRR op (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRR op (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int) (.vreg (aliasNum aliases ny) .int) := by
    change MInst.aluRRR op (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nx .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg ny .int)) = _
    rw [destination, resolve_vreg, resolve_vreg]
    rfl
  refine ⟨upd ρ d (resX (szOf ty.width) r), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨w', executed, world⟩ := seqRun_aluRRR refines (d := d) (w := w) computed
    exact ⟨w', by simpa only [code] using executed, world⟩
  · rw [upd_same]
    exact value
  · intro n different
    simp only [upd, different, ite_false]

/-- The valid immediate NOT form uses the original source bits. -/
theorem stock_not_imm_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} (operation : NotOp op)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (source : fr.getAs x ty = .ok u) {imm : ImmLogic}
    (immediate : ImmLogic.ofNat? imm.value (szOf ty.width) = some imm)
    (immValue : (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = v) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRImmLogic op (szOf ty.width) (.vreg d .int) (.vreg nx .int) imm).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,notOpVal op u v⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read rfl (getAs_ok source) mapped
  obtain ⟨r,computed,value⟩ := aluVal_holds_not operation (szOf_bits width) xValue immValue
  have code : (MInst.aluRRImmLogic op (szOf ty.width) (.vreg d .int) (.vreg nx .int) imm).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRImmLogic op (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int) imm := by
    change MInst.aluRRImmLogic op (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nx .int)) imm = _
    rw [fresh_reg bounded,resolve_vreg]
    rfl
  refine ⟨upd ρ d (resX (szOf ty.width) r), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (ispec_aluRRImmLogic (d := d) (rn := .vreg (aliasNum aliases nx) .int) (w := w)
        immediate operation.op6 computed)
    refine ⟨w', ?_, world⟩
    rw [code]
    simp only [seqRun,operands_aluRRImmLogic]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩] ρ =
        [ρ (aliasNum aliases nx)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]

/-- The LSL NOT form uses the source value without materializing its sunk shift. -/
theorem stock_not_shift_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} (operation : NotOp op)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x z nx nz d : Nat}
    (bounded : aliases.size ≤ d)
    (mappedX : ctx.valueReg? x = some (.vreg nx .int)) (mappedZ : ctx.valueReg? z = some (.vreg nz .int))
    (held : ValuesHeld (fun v => v = x ∨ v = z) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceZ : fr.getAs z ty = .ok v)
    {shift : ShiftOpAndAmt} (lsl : shift.op = .lsl) (amount : shift.amt < ty.width) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRRShift op (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg nz .int) shift).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,notOpVal op u (v <<< shift.amt)⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have zValue := held.read (Or.inr rfl) (getAs_ok sourceZ) mappedZ
  have shifted : (opnd (szOf ty.width) (ρ (aliasNum aliases nz)) <<< shift.amt).setWidth ty.width = v <<< shift.amt := by
    rw [BitVec.setWidth_shiftLeft_of_le (szOf_bits width),opnd_setWidth_eq (szOf_bits width) zValue]
  obtain ⟨r,computed,value⟩ := aluVal_holds_not operation (szOf_bits width) xValue shifted
  have code : (MInst.aluRRRShift op (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg nz .int) shift).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRRShift op (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int)
        (.vreg (aliasNum aliases nz) .int) shift := by
    change MInst.aluRRRShift op (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nx .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nz .int)) shift = _
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg]
    rfl
  refine ⟨upd ρ d (resX (szOf ty.width) r), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (ispec_aluRRRShift (d := d) (rn := .vreg (aliasNum aliases nx) .int)
        (rm := .vreg (aliasNum aliases nz) .int) (w := w)
        operation.op8 lsl (Nat.lt_of_lt_of_le amount (szOf_bits width)) computed)
    refine ⟨w', ?_, world⟩
    rw [code]
    simp only [seqRun,operands_aluRRRShift]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩,
        ⟨aliasNum aliases nz,.int,.use,.early,.reg⟩] ρ = [ρ (aliasNum aliases nx),ρ (aliasNum aliases nz)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]


end Backend.Stock.Proof.LogicalNot
