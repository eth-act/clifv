module

public import FV.Backend.Proof.StockDivImmResolved

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv.ImmResolvedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
inductive Case where | movz | movn | logical | lcf32 | lcf64
def width : Case → Nat | .movz => 8 | .movn => 64 | .logical => 32 | .lcf32 => 32 | .lcf64 => 64
def extension : Case → Nat | .lcf32 | .lcf64 => 0 | _ => 1
def literal : Case → Int | .movz => 9 | .lcf32 => 305419896 | .movn => -7 | .logical => 16711935 | .lcf64 => 81985529216486895
def expectedRule : Case → Rule
  | .movz => rule_inst_3742
  | .movn => rule_inst_3745
  | .logical => rule_inst_3751
  | .lcf32 => rule_inst_3786
  | .lcf64 => rule_inst_3790
private def framed : State := {sinkState with demand := #[2,1],sunk := #[true,false]}
private def aliases : Array (Option Nat) := #[some 1,none]
private theorem fixed (k : Nat) (nonzero : k ≠ 0) : aliasNum aliases k = k := by
  cases k with
  | zero => exact False.elim (nonzero rfl)
  | succ k =>
    cases k with
    | zero => exact chaseF_none rfl _
    | succ k =>
      apply chaseF_none
      rw [Array.getElem?_eq_none (by simp [aliases])]
      rfl
private theorem idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k := by
  intro k
  by_cases zero : k = 0
  · subst k; decide +kernel
  · rw [fixed k zero]
    exact fixed k zero
private def observed (fixture : Case) : Option Bool :=
  ((applyTerm program (Stock.sem sinkCtx) {} 2000 27 553
    (immArgs (width fixture) (extension fixture) (literal fixture))).run (framed,#[])).toOption.map
    (fun (out,_,trace) => out.isSome && decide (trace.toList.getLast? = some (expectedRule fixture).id))
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem observed_run (fixture : Case) : observed fixture = some true := by
  cases fixture <;> decide +kernel
end Kernel
/-- Every actual immediate rule has an alias-resolved machine execution witness
with nonzero scheduling fields, including both MOVK constant-loop sizes. -/
theorem stock_div_imm_resolved_witness (fixture : Case) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) :
    ∃ next trace ms d,
      (applyTerm program (Stock.sem sinkCtx) {} 2000 27 553
        (immArgs (width fixture) (extension fixture) (literal fixture))).run (framed,#[]) =
          .ok (some (.reg (.vreg d .int)),next,trace) ∧
      trace.toList.getLast? = some (expectedRule fixture).id ∧ next = {framed with base := next.base} ∧
      CodeShape framed.base next.base ms d framed.base.nextVreg ∧ d < next.base.nextVreg ∧
      ∀ ρ,∃ ρ' X,PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
        lo64 (ρ' d) = BitVec.ofNat 64 X ∧ X % 2^(width fixture) = u64 (literal fixture) % 2^(width fixture) ∧
        (width fixture ≠ 32 ∨ extension fixture = 0 ∨ u64 (literal fixture) < 2^32 →
          X = immVal (width fixture) (extension fixture == 0) (u64 (literal fixture))) ∧
        ∀ k,k < framed.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k := by
  have actual := observed_run fixture
  unfold observed at actual
  cases run : (applyTerm program (Stock.sem sinkCtx) {} 2000 27 553
      (immArgs (width fixture) (extension fixture) (literal fixture))).run (framed,#[]) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    cases out with
    | none => simp only [run,Except.toOption,Option.map_some,Option.isSome_none] at actual; cases actual
    | some out =>
      have fired : trace.toList.getLast? = some (expectedRule fixture).id := by
        simpa only [run,Except.toOption,Option.map_some,Option.some.injEq,Option.isSome_some,Bool.true_and,decide_eq_true_eq] using actual
      obtain ⟨ms,d,frame,output,shape,bound,values⟩ := stock_div_imm_resolved data_program sinkCtx (cfg := {}) rfl
        refines (by cases fixture <;> decide) (by cases fixture <;> decide) (n := 1960) run
        (aliases := aliases) (by decide) idem
      exact ⟨next,trace,ms,d,by rw [← output],fired,frame,shape,bound,values⟩
end Backend.Stock.Proof.ScalarDiv.ImmResolvedWitness
