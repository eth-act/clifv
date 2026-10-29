module

public import FV.Backend.Proof.StockDivMinimumResolved

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def minimumState : State := {sinkState with base := {sinkState.base with nextVreg := 2}}
private def minimumAliases : Array (Option Nat) := #[some 1,none]
private def minimumRegs (n : Nat) (minimum : Bool) (_ : Nat) : CV :=
  resX (szOf n) ((if minimum then BitVec.intMin n else (1 : BitVec n)).signExtend (szOf n).bits)
/-- All four actual minimum-helper paths execute under nonidentity source
aliases, including both minimum and nonminimum source operands. -/
theorem stock_div_minimum_source_witness (n : Nat)
    (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (minimum : Bool) :
    ∃ next out trace ms check ρ',ApplyInternal program (Stock.sem sinkCtx) {} 199 27 562
      [.ty (.int n),.reg (.vreg 0 .int)] (minimumState,#[]) out (next,trace) ∧
      out = .reg (.vreg check .int) ∧ Frag minimumState.base next.base ms ∧
      PRun (fun _ => True) ispec (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve minimumAliases (minimumAliases.size+1)))) (minimumRegs n minimum) ρ' ∧
      (opnd (szOf n) (ρ' (aliasNum minimumAliases check)) = BitVec.intMin (szOf n).bits ↔
        (if minimum then BitVec.intMin n else (1 : BitVec n)) = BitVec.intMin n) ∧
      ∀ k,k < minimumState.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = minimumRegs n minimum k := by
  obtain ⟨trace,run⟩ := stock_div_intmin_helper data_program sinkCtx (cfg := {}) rfl width minimumState #[] 140 (.vreg 0 .int)
  have actual : ApplyInternal program (Stock.sem sinkCtx) {} 199 27 562
      [.ty (.int n),.reg (.vreg 0 .int)] (minimumState,#[]) _ (_,trace) := run
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have operand : DivOpnd true (if minimum then BitVec.intMin n else (1 : BitVec n))
      (minimumRegs n minimum (aliasNum minimumAliases 0)) := by
    unfold DivOpnd
    cases minimum <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨ms,check,ρ',output,fragment,location,execution,reflected,kept⟩ :=
    stock_div_minimum_source_values data_program sinkCtx self width (by decide) actual (by decide) operand
  exact ⟨_,_,trace,ms,check,ρ',actual,output,fragment,execution,reflected,kept⟩
end Backend.Stock.Proof.ScalarDiv
