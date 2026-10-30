import FV.Backend.Proof.StockShiftSemantics
import FV.Backend.Proof.StockShiftRhs
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def function : Clif.Function := {
  name := "stock_shift_rhs",sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(8,.i64)],body := [],term := .ret [7]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private theorem mapped : built.1.valueReg? 8 = some (.vreg 193 .int) := rfl
private theorem safe : DemandAllowed built.1 built.2.2 8 := by
  intro i h
  change none = some i at h
  cases h
private def shiftTag (right arithmetic : Bool) : Nat := if right then (if arithmetic then 17 else 16) else 18
private def shiftOp (right arithmetic : Bool) : ALUOp := if right then (if arithmetic then .asr else .lsr) else .lsl
private theorem tag (right arithmetic : Bool) : ALUOp.ofIdx? (shiftTag right arithmetic) = some (shiftOp right arithmetic) := by
  cases right <;> cases arithmetic <;> rfl

/-- Actual immediate RHS executions exist for every scalar width and shift
operation, independently of a materialized count register. -/
theorem stock_shift_imm_rhs_witness (right arithmetic : Bool) (w : Nat)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    ∃ trace,(evalExpr program (Stock.sem built.1) {} 110 rule_lower_1631.rhs
      (env5 (.data 59 (shiftTag right arithmetic) []) (.ty (.int w)) (.reg (.vreg 192 .int)) (.int 3) (.op (.immShift 3)))).run (built.2.2,#[]) =
      .ok (some (.reg (built.2.2.base.fresh .int).1),
        {built.2.2 with base := (built.2.2.base.fresh .int).2.emit (.aluRRImmShift (shiftOp right arithmetic) (szOf w) (built.2.2.base.fresh .int).1 (.vreg 192 .int) 3)},trace) := by
  exact stock_shift_imm_rhs data_program built.1 (by rcases width with rfl | rfl | rfl | rfl <;> decide) (tag right arithmetic) built.2.2 #[] 80 (.vreg 192 .int) 3 3

/-- Both register-count selections are inhabited for every shift operation
using the real dense register mapping and original Stock demand guard. -/
theorem stock_shift_rrr_rhs_witness (right arithmetic wide : Bool) :
    ∃ trace,(evalExpr program (Stock.sem built.1) {} 120 (shiftRegisterRule wide).rhs
      (env3 (.data 59 (shiftTag right arithmetic) []) (.reg (.vreg 192 .int)) (.value 8))).run (built.2.2,#[]) =
      .ok (some (.reg (built.2.2.base.fresh .int).1),
        {built.2.2.mark 8 with base := (built.2.2.base.fresh .int).2.emit (.aluRRR (shiftOp right arithmetic) (szOf (shiftWidth wide)) (built.2.2.base.fresh .int).1 (.vreg 192 .int) (.vreg 193 .int))},trace) := by
  exact stock_shift_rrr_rhs data_program built.1 wide (tag right arithmetic) mapped built.2.2 safe #[] 80 (.vreg 192 .int)

/-- Narrow register-count selections emit the complete mask/shift pair,
including the scratch allocation and marked original amount request. -/
theorem stock_shift_mask_rhs_witness (right arithmetic : Bool) (w : Nat) (width : w = 8 ∨ w = 16) :
    ∃ trace,(evalExpr program (Stock.sem built.1) {} 140 rule_lower_1612.rhs
      (shiftMaskEnv (shiftTag right arithmetic) w (.vreg 192 .int) 8)).run (built.2.2,#[]) =
      .ok (some (.reg (.vreg (built.2.2.base.nextVreg+1) .int)),
        {built.2.2.mark 8 with base := (((built.2.2.base.fresh .int).2.emit (.aluRRImmLogic .and .size32 (built.2.2.base.fresh .int).1 (.vreg 193 .int) ⟨w-1,.size32⟩)).fresh .int).2.emit (.aluRRR (shiftOp right arithmetic) .size32 (.vreg (built.2.2.base.nextVreg+1) .int) (.vreg 192 .int) (built.2.2.base.fresh .int).1)},trace) := by
  exact stock_shift_mask_rhs data_program built.1 width (tag right arithmetic) mapped built.2.2 safe #[] 80 (.vreg 192 .int)
private def machineRegs (k : Nat) : CV :=
  if k = 192 then BitVec.ofNat 128 (2^100+165)
  else if k = 193 then BitVec.ofNat 128 (2^112+273) else 0
private def amount : Clif.Val := .ofInt .i64 273
private def maskWidth (wide : Bool) : Nat := if wide then 16 else 8
private theorem operation (right arithmetic : Bool) : IsShift (shiftOp right arithmetic) := by
  cases right <;> cases arithmetic <;> simp [shiftOp,IsShift]

/-- The full hypotheses and conclusions of all three resolved machine
contracts are simultaneously inhabited, for every operation and both register
and narrow widths. Original count bits and deliberately dirty upper bits are
included; both writes of the narrow fragment are checked. -/
theorem stock_shift_semantics_witness (right arithmetic wide narrowWide : Bool) :
    (∃ ρ',PRun (fun _ => True) ispec
      [(MInst.aluRRImmShift (shiftOp right arithmetic) .size32 (.vreg 194 .int) (.vreg 192 .int) 3).mapRegs
        (Backend.lowerFunction.resolve #[] 1)] machineRegs ρ' ∧
      opnd .size32 (ρ' 194) = shiftF (shiftOp right arithmetic) (opnd .size32 (machineRegs 192)) 3 ∧
      ∀ n,n ≠ 194 → ρ' n = machineRegs n) ∧
    (∃ ρ',PRun (fun _ => True) ispec
      [(MInst.aluRRR (shiftOp right arithmetic) (szOf (shiftWidth wide)) (.vreg 194 .int) (.vreg 192 .int) (.vreg 193 .int)).mapRegs
        (Backend.lowerFunction.resolve #[] 1)] machineRegs ρ' ∧
      opnd (szOf (shiftWidth wide)) (ρ' 194) = shiftF (shiftOp right arithmetic)
        (opnd (szOf (shiftWidth wide)) (machineRegs 192)) (amount.bits.toNat % shiftWidth wide) ∧
      ∀ n,n ≠ 194 → ρ' n = machineRegs n) ∧
    (∃ ρ',PRun (fun _ => True) ispec
      ([MInst.aluRRImmLogic .and .size32 (.vreg 194 .int) (.vreg 193 .int) ⟨maskWidth narrowWide-1,.size32⟩,
        .aluRRR (shiftOp right arithmetic) .size32 (.vreg 195 .int) (.vreg 192 .int) (.vreg 194 .int)].map
          (·.mapRegs (Backend.lowerFunction.resolve #[] 1))) machineRegs ρ' ∧
      opnd .size32 (ρ' 195) = shiftF (shiftOp right arithmetic) (opnd .size32 (machineRegs 192))
        (amount.bits.toNat % maskWidth narrowWide) ∧
      ∀ n,n ≠ 194 → n ≠ 195 → ρ' n = machineRegs n) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have held : VHolds amount (machineRegs 193) := by unfold amount machineRegs VHolds; decide +kernel
  have bounds : (#[] : Array (Option Nat)).size ≤ 194 := by decide
  have fresh : aliasNum (#[] : Array (Option Nat)) 192 = 192 := rfl
  have immediate := stock_shift_imm_resolved self (operation right arithmetic) (w := 32) (by simp [IW])
    (ρ := machineRegs) (a := 192) bounds (amount := 3) (by decide)
  have register := stock_shift_rrr_resolved self (operation right arithmetic)
    (w := shiftWidth wide) (by cases wide <;> simp [shiftWidth]) (ρ := machineRegs) (a := 192) bounds held
  have maskValid : ImmLogic.ofNat? (maskWidth narrowWide-1) .size32 = some ⟨maskWidth narrowWide-1,.size32⟩ := by
    cases narrowWide <;> rfl
  have masked := stock_shift_mask_resolved self (operation right arithmetic)
    (w := maskWidth narrowWide) (by cases narrowWide <;> simp [maskWidth]) (ρ := machineRegs)
    (a := 192) bounds (by rw [fresh]; decide) held maskValid
  exact ⟨by simpa [szOf,fresh] using immediate,
    by simpa [fresh] using register,by simpa [fresh] using masked⟩
end Backend.Stock.Proof.ScalarShift
