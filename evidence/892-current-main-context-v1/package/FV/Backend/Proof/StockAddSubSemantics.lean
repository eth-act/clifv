import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.IselFamALUAExt
namespace Backend.Stock.Proof.ScalarAddSub
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

theorem stock_addsub_shift_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (subtract : Bool)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x z nx nz d : Nat}
    (bounded : aliases.size ≤ d)
    (mappedX : ctx.valueReg? x = some (.vreg nx .int)) (mappedZ : ctx.valueReg? z = some (.vreg nz .int))
    (held : ValuesHeld (fun v => v = x ∨ v = z) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceZ : fr.getAs z ty = .ok v)
    {shift : ShiftOpAndAmt} (lsl : shift.op = .lsl) (amount : shift.amt < ty.width) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRRShift (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg nz .int) shift).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u (v <<< shift.amt)⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have zValue := held.read (Or.inr rfl) (getAs_ok sourceZ) mappedZ
  have shifted : (opnd (szOf ty.width) (ρ (aliasNum aliases nz)) <<< shift.amt).setWidth ty.width = v <<< shift.amt := by
    rw [BitVec.setWidth_shiftLeft_of_le (szOf_bits width),opnd_setWidth_eq (szOf_bits width) zValue]
  have pair : ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.add,.iadd) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.sub,.isub) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.and,.band) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.orr,.bor) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.eor,.bxor) := by cases subtract <;> simp
  obtain ⟨r,computed,value⟩ := aluVal_holds_B pair (szOf_bits width) xValue shifted
  have code : (MInst.aluRRRShift (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg nz .int) shift).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRRShift (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int)
        (.vreg (aliasNum aliases nz) .int) shift := by
    change MInst.aluRRRShift (if subtract then .sub else .add) (szOf ty.width)
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
        (by cases subtract <;> simp) lsl (Nat.lt_of_lt_of_le amount (szOf_bits width)) computed)
    refine ⟨w', ?_, world⟩
    rw [code]
    simp only [seqRun,operands_aluRRRShift]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩,
        ⟨aliasNum aliases nz,.int,.use,.early,.reg⟩] ρ = [ρ (aliasNum aliases nx),ρ (aliasNum aliases nz)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]

/-- Immediate execution uses the original source value through final aliases;
only the fresh destination changes, including for narrow values with dirty upper bits. -/
theorem stock_addsub_imm_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (subtract : Bool)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (source : fr.getAs x ty = .ok u) {imm : Imm12}
    (valid : imm.bits < 4096)
    (immediate : (BitVec.ofNat (szOf ty.width).bits imm.value).setWidth ty.width = v) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRImm12 (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg nx .int) imm).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' d) ∧
      ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read rfl (getAs_ok source) mapped
  have pair : ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.add,.iadd) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.sub,.isub) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.and,.band) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.orr,.bor) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.eor,.bxor) := by cases subtract <;> simp
  obtain ⟨r,computed,value⟩ := aluVal_holds_B pair (szOf_bits width) xValue immediate
  have code : (MInst.aluRRImm12 (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg nx .int) imm).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRImm12 (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int) imm := by
    change MInst.aluRRImm12 (if subtract then .sub else .add) (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nx .int)) imm = _
    rw [fresh_reg bounded,resolve_vreg]
    rfl
  have execution : ∀ w, ispec
      (.aluRRImm12 (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int)
        (.vreg (aliasNum aliases nx) .int) imm) [ρ (aliasNum aliases nx)] w =
      some ([resX (szOf ty.width) r],w,.next) := by
    intro w
    cases subtract
    · simp only [Bool.false_eq_true,ite_false] at computed ⊢
      rw [ispec_aluRRImm12_add valid]
      simp only [aluVal] at computed
      cases computed
      rfl
    · simp only [ite_true] at computed ⊢
      rw [ispec_aluRRImm12_sub valid]
      simp only [aluVal] at computed
      cases computed
      rfl
  refine ⟨upd ρ d (resX (szOf ty.width) r), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _ (execution w)
    refine ⟨w', ?_, world⟩
    rw [code]
    simp only [seqRun,operands_aluRRImm12]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩] ρ =
      [ρ (aliasNum aliases nx)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]
theorem stock_addsub_extend_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (subtract : Bool)
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x z nx nz d : Nat}
    (bounded : aliases.size ≤ d)
    (mappedX : ctx.valueReg? x = some (.vreg nx .int)) (mappedZ : ctx.valueReg? z = some (.vreg nz .int))
    (held : ValuesHeld (fun v => v = x ∨ v = z) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u)
    {a : Clif.Val} (sourceZ : fr.regs z = some a) {cop : Clif.ExtendOp} {b : Nat} {e : ExtendOp}
    (extended : extOpOf cop b = some e) (sourceWidth : a.ty.width = b) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRRExtend (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg nz .int) e).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u (extVal cop ty.width a.bits)⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have zValue := held.read (Or.inr rfl) sourceZ mappedZ
  have extendedValue := extendVal_holds extended sourceWidth zValue (n := (szOf ty.width).bits) (szOf_bits width)
  have pair : ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.add,.iadd) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.sub,.isub) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.and,.band) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.orr,.bor) ∨
      ((if subtract then ALUOp.sub else .add),(if subtract then Clif.BinaryOp.isub else .iadd)) = (.eor,.bxor) := by cases subtract <;> simp
  obtain ⟨r,computed,value⟩ := aluVal_holds_B pair (szOf_bits width) xValue extendedValue
  have code : (MInst.aluRRRExtend (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg nz .int) e).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRRExtend (if subtract then .sub else .add) (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int)
        (.vreg (aliasNum aliases nz) .int) e := by
    change MInst.aluRRRExtend (if subtract then .sub else .add) (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nx .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nz .int)) e = _
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg]
    rfl
  refine ⟨upd ρ d (resX (szOf ty.width) r), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (ispec_aluRRRExtend (d := d) (rn := .vreg (aliasNum aliases nx) .int)
        (rm := .vreg (aliasNum aliases nz) .int) (w := w)
        (by cases subtract <;> simp) computed)
    refine ⟨w', ?_, world⟩
    rw [code]
    simp only [seqRun,operands_aluRRRExtend]
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩,
        ⟨aliasNum aliases nz,.int,.use,.early,.reg⟩] ρ = [ρ (aliasNum aliases nx),ρ (aliasNum aliases nz)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]; exact value
  · intro n different; simp only [upd,different,ite_false]

end Backend.Stock.Proof.ScalarAddSub
