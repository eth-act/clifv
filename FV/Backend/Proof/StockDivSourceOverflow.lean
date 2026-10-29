module

public import FV.Backend.Proof.StockDivResolvedGuards
public import FV.Backend.Proof.StockDivIntmin

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The alias-resolved guard recognizes exactly original signed source overflow;
minimum-check reflection is produced by dividend preparation. -/
theorem stock_div_overflow_source_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n : Nat} (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    {u v : BitVec n} {aliases : Array (Option Nat)} {ρ : Nat → CV} {check divisor : Nat}
    (operand : DivOpnd true v (ρ (aliasNum aliases divisor)))
    (minimum : opnd (szOf n) (ρ (aliasNum aliases check)) = BitVec.intMin (szOf n).bits ↔ u = BitVec.intMin n)
    (world : Arm.ArmState) :
    (u = BitVec.intMin n ∧ v = BitVec.allOnes n → TrapRun isem
      ((ovfCheck (szOf n) check divisor).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world .intOvf) ∧
    (¬(u = BitVec.intMin n ∧ v = BitVec.allOnes n) → Runs F isem
      ((ovfCheck (szOf n) check divisor).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ => ρ' = ρ)) := by
  have minusOne := stock_div_operand_allOnes width operand
  have outcomes := stock_div_overflow_guard_resolved refines (szOf n) check divisor aliases ρ world
  exact ⟨fun ⟨a,b⟩ => outcomes.1 ⟨minusOne.mpr b,minimum.mpr a⟩,
    fun no => outcomes.2 (fun ⟨a,b⟩ => no ⟨minimum.mp b,minusOne.mp a⟩)⟩
private def sourceAliases : Array (Option Nat) := #[some 1,none,some 3,none]
private def sourceRegs (n : Nat) (trapping : Bool) (key : Nat) : CV :=
  if key = 1 then resX (szOf n) (if trapping then BitVec.intMin (szOf n).bits else 1)
  else if key = 3 then resX (szOf n) (BitVec.allOnes (szOf n).bits) else 0
/-- Source overflow and normal outcomes are inhabited at all four source widths
through distinct nonidentity check and divisor aliases. -/
theorem stock_div_source_overflow_witness (n : Nat)
    (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (trapping : Bool) (world : Arm.ArmState) :
    ∃ ρ,(trapping = true → TrapRun ispec ((ovfCheck (szOf n) 0 2).map (·.mapRegs
      (Backend.lowerFunction.resolve sourceAliases (sourceAliases.size+1)))) ρ world .intOvf) ∧
    (trapping = false → Runs (fun _ => True) ispec ((ovfCheck (szOf n) 0 2).map (·.mapRegs
      (Backend.lowerFunction.resolve sourceAliases (sourceAliases.size+1)))) ρ world (fun ρ' _ => ρ' = ρ)) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have operand : DivOpnd true (BitVec.allOnes n) (sourceRegs n trapping (aliasNum sourceAliases 2)) := by
    unfold DivOpnd
    cases trapping <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  have minimum : opnd (szOf n) (sourceRegs n trapping (aliasNum sourceAliases 0)) = BitVec.intMin (szOf n).bits ↔
      (if trapping then BitVec.intMin n else (1 : BitVec n)) = BitVec.intMin n := by
    cases trapping <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  have outcomes := stock_div_overflow_source_resolved self width operand minimum world
  refine ⟨sourceRegs n trapping,?_,?_⟩
  · intro yes; subst trapping; exact outcomes.1 ⟨rfl,rfl⟩
  · intro no; subst trapping
    apply outcomes.2
    rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
end Backend.Stock.Proof.ScalarDiv
