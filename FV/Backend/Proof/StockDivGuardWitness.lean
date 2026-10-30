import FV.Backend.Proof.StockDivGuardSemantics
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem self_refines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
private def overflowRegs (sz : OperandSize) (trapping : Bool) (key : Nat) : CV :=
  if key = 192 then resX sz (BitVec.intMin sz.bits)
  else if key = 193 then resX sz (if trapping then BitVec.allOnes sz.bits else 1) else 0
/-- Actual overflow guard runs inhabit both trap and normal outcomes at32/64;
all registers are preserved on normal execution. Source-record composition remains
separate from this machine-guard witness. -/
theorem stock_div_overflow_guard_witness (sz : OperandSize) (w : Arm.ArmState) :
    TrapRun ispec (ovfCheck sz 192 193) (overflowRegs sz true) w .intOvf ∧
    Runs (fun _ => True) ispec (ovfCheck sz 192 193) (overflowRegs sz false) w
      (fun ρ' _ => ρ' = overflowRegs sz false) := by
  have traps := (stock_div_overflow_guard_run self_refines sz 192 193 (overflowRegs sz true) w).1
  have normal := (stock_div_overflow_guard_run self_refines sz 192 193 (overflowRegs sz false) w).2
  constructor
  · apply traps
    simp only [overflowRegs,ite_true,ite_false,Bool.true_eq_false,Nat.reduceEqDiff,cmp_opnd_resX]
    exact ⟨trivial,trivial⟩
  · apply normal
    simp only [overflowRegs,ite_true,ite_false,Bool.false_eq_true,Nat.reduceEqDiff,cmp_opnd_resX]
    cases sz <;> decide +kernel

/-- Actual zero guards inhabit both outcomes for signed/unsigned original
operand widths8/16/32/64, without excluding zero from the input domain. -/
theorem stock_div_zero_guard_witness (signed : Bool) (n : Nat)
    (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (w : Arm.ArmState) :
    TrapRun ispec [.trapIf (.zero (.vreg 192 .int) (szOf n)) .intDivz] (fun _ => 0) w .intDivz ∧
    Runs (fun _ => True) ispec [.trapIf (.zero (.vreg 192 .int) (szOf n)) .intDivz]
      (fun _ => 1) w (fun ρ' _ => ρ' = (fun _ => 1)) := by
  have zero : DivOpnd signed (0#n) (0 : CV) := by
    cases signed <;> rcases width with rfl | rfl | rfl | rfl <;> rfl
  have nonzero : DivOpnd signed (1#n) (1 : CV) := by
    cases signed <;> rcases width with rfl | rfl | rfl | rfl <;> rfl
  have positive : 1#n ≠ 0#n := by rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  exact ⟨(stock_div_zero_guard_run self_refines (ρ := fun _ => 0) (key := 192) (by omega) zero w).1 rfl,
    (stock_div_zero_guard_run self_refines (ρ := fun _ => 1) (key := 192) (by omega) nonzero w).2 positive⟩
end Backend.Stock.Proof.ScalarDiv
