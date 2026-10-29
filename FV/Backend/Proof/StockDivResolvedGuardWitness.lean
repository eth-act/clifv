module

public import FV.Backend.Proof.StockDivResolvedGuards

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def aliases : Array (Option Nat) := #[some 1,none,some 3,none]
private def zeroRegs (signed trapping : Bool) (n : Nat) (_ : Nat) : CV :=
  let b : BitVec n := if trapping then 0 else 1
  resX (szOf n) (if signed then b.signExtend (szOf n).bits else b.zeroExtend (szOf n).bits)
/-- Nontrivial aliases inhabit both zero-guard outcomes for signed/unsigned
8/16/32/64 source operands, preserving all registers on normal execution. -/
theorem stock_div_zero_alias_witness (signed trapping : Bool) (n : Nat)
    (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (world : Arm.ArmState) :
    ∃ ρ,(trapping = true → TrapRun ispec
      [(.trapIf (.zero (.vreg 0 .int) (szOf n)) .intDivz : MInst).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ world .intDivz) ∧
      (trapping = false → Runs (fun _ => True) ispec
      [(.trapIf (.zero (.vreg 0 .int) (szOf n)) .intDivz : MInst).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ world (fun ρ' _ => ρ' = ρ)) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have operand : DivOpnd signed (if trapping then (0 : BitVec n) else 1)
      (zeroRegs signed trapping n (aliasNum aliases 0)) := by
    unfold DivOpnd
    cases signed <;> cases trapping <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  have outcomes := stock_div_zero_guard_resolved self (by omega) operand world
  refine ⟨zeroRegs signed trapping n,?_,?_⟩
  · intro yes; subst trapping
    exact outcomes.1 rfl
  · intro no; subst trapping
    exact outcomes.2 (by rcases width with rfl | rfl | rfl | rfl <;> decide +kernel)
private def overflowRegs (sz : OperandSize) (trapping : Bool) (key : Nat) : CV :=
  if key = 1 then resX sz (if trapping then BitVec.intMin sz.bits else 1)
  else if key = 3 then resX sz (BitVec.allOnes sz.bits) else 0
/-- Both overflow outcomes at32/64 are inhabited through separate check/divisor
aliases, without restricting the original signed input domain. -/
theorem stock_div_overflow_alias_witness (sz : OperandSize) (trapping : Bool) (world : Arm.ArmState) :
    ∃ ρ,(trapping = true → TrapRun ispec ((ovfCheck sz 0 2).map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world .intOvf) ∧
      (trapping = false → Runs (fun _ => True) ispec ((ovfCheck sz 0 2).map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ => ρ' = ρ)) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have outcomes := stock_div_overflow_guard_resolved self sz 0 2 aliases (overflowRegs sz trapping) world
  refine ⟨overflowRegs sz trapping,?_,?_⟩
  · intro yes; subst trapping
    exact outcomes.1 (by cases sz <;> decide +kernel)
  · intro no; subst trapping
    exact outcomes.2 (by cases sz <;> decide +kernel)
end Backend.Stock.Proof.ScalarDiv
