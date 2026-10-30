import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.IselFamALUALogic
import FV.Backend.Proof.StockLogicalForms

/-! Logical immediate/shift execution under mapped and alias-resolved registers. -/
namespace Backend.Stock.Proof.LogicalSemantics
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

/-- An alias-resolved logical immediate instruction computes the source binary
value and writes only its fresh destination. -/
theorem stock_logical_imm_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} {cop : Clif.BinaryOp} (operation : LogicPair op cop)
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
      VHolds ⟨ty,Clif.Sem.binary cop u v⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read rfl (getAs_ok source) mapped
  obtain ⟨r,computed,value⟩ := aluVal_holds_B operation.alu (szOf_bits width) xValue immValue
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

/-- An alias-resolved LSL logical instruction computes the binary value of its
shifted source operand and writes only its fresh destination. -/
theorem stock_logical_shift_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} {cop : Clif.BinaryOp} (operation : LogicPair op cop)
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
      VHolds ⟨ty,Clif.Sem.binary cop u (v <<< shift.amt)⟩ (ρ' d) ∧ ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have zValue := held.read (Or.inr rfl) (getAs_ok sourceZ) mappedZ
  have shifted : (opnd (szOf ty.width) (ρ (aliasNum aliases nz)) <<< shift.amt).setWidth ty.width = v <<< shift.amt := by
    rw [BitVec.setWidth_shiftLeft_of_le (szOf_bits width),opnd_setWidth_eq (szOf_bits width) zValue]
  obtain ⟨r,computed,value⟩ := aluVal_holds_B operation.alu (szOf_bits width) xValue shifted
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

private def witnessState : State := {sinkState with
  base := ⟨195,Array.replicate 195 .int,#[],0⟩
  demand := Array.replicate 101 0
  sunk := #[] }
private def witnessRegs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private def witnessFrame (ctx : Ctx) (ty : Clif.Ty) : Clif.Frame := {
  func := ctx.func
  regs := fun x => if x = 7 then some (.ofInt ty 7) else if x = 31 then some (.ofInt ty 5) else none
  slots := [],body := [],term := .ret [100] }
private def witnessImm (ty : Clif.Ty) : ImmLogic := ⟨255,szOf ty.width⟩
private def witnessShift : ShiftOpAndAmt := ⟨.lsl,3⟩
private theorem witnessSafe (ctx : Ctx) (x : Nat) : DemandAllowed ctx witnessState x := by
  intro i _
  change (#[] : Array Bool)[i]! = false
  simp

/-- At32/64 bits, actual mapped Stock immediate/shift RHS execution establishes
its machine result and preserves both inputs for each commutative logical op. -/
theorem stock_logical_semantics_witness (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64)
    (k : Nat) (op : ALUOp) (cop : Clif.BinaryOp) (tag : ALUOp.ofIdx? k = some op)
    (operation : LogicPair op cop) :
    ∃ (ctx : Ctx) (si ss : State) (ti ts : Array RuleId) (ρi ρs : Nat → CV),
      ctx.valueReg? 7 = some (.vreg 192 .int) ∧ ctx.valueReg? 31 = some (.vreg 193 .int) ∧
      (evalExpr program (Stock.sem ctx) {} 40 rule_inst_3920.rhs
        (env5 (.data 59 k []) (.ty (.int ty.width)) (.value 7) (.int 255) (.op (.immLogic (witnessImm ty))))).run
          (witnessState,#[]) = .ok (some (.reg (.vreg 195 .int)),si,ti) ∧
      (evalExpr program (Stock.sem ctx) {} 40 rule_inst_3928.rhs
        (env6 (.data 59 k []) (.ty (.int ty.width)) (.value 7) (.value 31) (.int 3) (.op (.shiftOpAndAmt witnessShift)))).run
          (witnessState,#[]) = .ok (some (.reg (.vreg 195 .int)),ss,ts) ∧
      PRun (fun _ => True) ispec si.base.emitted.toList witnessRegs ρi ∧
      PRun (fun _ => True) ispec ss.base.emitted.toList witnessRegs ρs ∧
      VHolds ⟨ty,Clif.Sem.binary cop (BitVec.ofInt ty.width 7) (BitVec.ofNat ty.width 255)⟩ (ρi 195) ∧
      VHolds ⟨ty,Clif.Sem.binary cop (BitVec.ofInt ty.width 7) (BitVec.ofInt ty.width 5 <<< 3)⟩ (ρs 195) ∧
      ρi 192 = 7 ∧ ρi 193 = 5 ∧ ρs 192 = 7 ∧ ρs 193 = 5 := by
  obtain ⟨ctx,info,ignored,ignoredTrace,ignoredRegs,_,_,_,_,mx,my,_⟩ := stock_alu_roots_witness false ty supported
  have width : ty.width ≤ 64 := by rcases supported with rfl | rfl <;> decide
  obtain ⟨ti,ri⟩ := LogicalForms.stock_rhs_3920 data_program ctx (cfg := {}) rfl tag mx width witnessState
    (witnessSafe ctx 7) #[] 0 (kk := 255) (imm := witnessImm ty)
  obtain ⟨ts,rs⟩ := LogicalForms.stock_rhs_3928 data_program ctx (cfg := {}) rfl tag mx my width witnessState
    (witnessSafe ctx 7) (witnessSafe ctx 31) #[] 0 (kk := 3) (sh := witnessShift)
  have held : ValuesHeld (fun z => z = 7 ∨ z = 31) ctx (witnessFrame ctx ty)
      (fun n => witnessRegs (aliasNum #[] n)) := by
    intro z required val lookup
    rcases required with rfl | rfl
    · change some (Clif.Val.ofInt ty 7) = some val at lookup
      cases lookup
      refine ⟨192,mx,?_⟩
      change VHolds (.ofInt ty 7) 7
      rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
    · change some (Clif.Val.ofInt ty 5) = some val at lookup
      cases lookup
      refine ⟨193,my,?_⟩
      change VHolds (.ofInt ty 5) 5
      rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
  have sourceX : (witnessFrame ctx ty).getAs 7 ty = .ok (BitVec.ofInt ty.width 7) := by
    rcases supported with rfl | rfl <;> rfl
  have sourceZ : (witnessFrame ctx ty).getAs 31 ty = .ok (BitVec.ofInt ty.width 5) := by
    rcases supported with rfl | rfl <;> rfl
  have imm : ImmLogic.ofNat? (witnessImm ty).value (szOf ty.width) = some (witnessImm ty) := by
    rcases supported with rfl | rfl <;> decide +kernel
  have immValue : (BitVec.ofNat (szOf ty.width).bits (witnessImm ty).value).setWidth ty.width =
      BitVec.ofNat ty.width 255 := by
    rcases supported with rfl | rfl <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρi,ei,vi,ki⟩ := stock_logical_imm_resolved self operation width (aliases := #[]) (ρ := witnessRegs)
    (d := 195) (by decide) mx (fun z h => held z (Or.inl h)) sourceX imm immValue
  obtain ⟨ρs,es,vs,ks⟩ := stock_logical_shift_resolved self operation width (aliases := #[]) (ρ := witnessRegs)
    (d := 195) (by decide) mx my held sourceX sourceZ (shift := witnessShift) rfl
    (by rcases supported with rfl | rfl <;> decide)
  refine ⟨ctx,_,_,ti,ts,ρi,ρs,mx,my,ri,rs,?_,?_,vi,vs,?_,?_,?_,?_⟩
  · simpa [witnessState,LState.fresh,LState.emit,State.mark,MInst.mapRegs,
      Backend.lowerFunction.resolve,chaseF] using ei
  · simpa [witnessState,LState.fresh,LState.emit,State.mark,MInst.mapRegs,
      Backend.lowerFunction.resolve,chaseF] using es
  · exact (ki 192 (by decide)).trans rfl
  · exact (ki 193 (by decide)).trans rfl
  · exact (ks 192 (by decide)).trans rfl
  · exact (ks 193 (by decide)).trans rfl

end Backend.Stock.Proof.LogicalSemantics
