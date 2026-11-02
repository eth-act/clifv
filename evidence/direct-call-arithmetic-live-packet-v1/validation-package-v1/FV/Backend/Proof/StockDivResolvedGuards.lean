import FV.Backend.Proof.StockDivGuardSemantics
import FV.Backend.Proof.StockAliasSemantics
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Final aliases preserve both actual zero-guard outcomes and the complete
register state on the normal path, including aliased source divisors. -/
theorem stock_div_zero_guard_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {n : Nat} (width : n ≤ 64) {signed : Bool}
    {b : BitVec n} {aliases : Array (Option Nat)} {ρ : Nat → CV} {key : Nat}
    (operand : DivOpnd signed b (ρ (aliasNum aliases key))) (world : Arm.ArmState) :
    (b = 0#n → TrapRun isem
      [(.trapIf (.zero (.vreg key .int) (szOf n)) .intDivz : MInst).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ world .intDivz) ∧
    (b ≠ 0#n → Runs F isem
      [(.trapIf (.zero (.vreg key .int) (szOf n)) .intDivz : MInst).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ world (fun ρ' _ => ρ' = ρ)) := by
  have code : (.trapIf (.zero (.vreg key .int) (szOf n)) .intDivz : MInst).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .trapIf (.zero (.vreg (aliasNum aliases key) .int) (szOf n)) .intDivz := by
    change MInst.trapIf (.zero (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg key .int)) _) _ = _
    rw [resolve_vreg]; rfl
  rw [code]
  exact stock_div_zero_guard_run refines width operand world
/-- The complete add-flags/conditional-compare/overflow-trap fragment resolves
both operands through final aliases and retains trap and normal outcomes. -/
theorem stock_div_overflow_guard_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (sz : OperandSize) (check divisor : Nat)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) (world : Arm.ArmState) :
    (opnd sz (ρ (aliasNum aliases divisor)) = BitVec.allOnes sz.bits ∧
      opnd sz (ρ (aliasNum aliases check)) = BitVec.intMin sz.bits →
      TrapRun isem ((ovfCheck sz check divisor).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world .intOvf) ∧
    (¬ (opnd sz (ρ (aliasNum aliases divisor)) = BitVec.allOnes sz.bits ∧
      opnd sz (ρ (aliasNum aliases check)) = BitVec.intMin sz.bits) →
      Runs F isem ((ovfCheck sz check divisor).map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ => ρ' = ρ)) := by
  have code : (ovfCheck sz check divisor).map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      ovfCheck sz (aliasNum aliases check) (aliasNum aliases divisor) := by
    simp only [ovfCheck,List.map_cons,List.map_nil,MInst.mapRegs,resolve_vreg]
    rfl
  rw [code]
  exact stock_div_overflow_guard_run refines sz _ _ ρ world
end Backend.Stock.Proof.ScalarDiv
