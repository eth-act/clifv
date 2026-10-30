import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.StockConditionalEmptyTrapSource

namespace Backend.Stock.Proof.ConditionalValues.EmptyTrapFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

private theorem scope : LowerScope function := lowerScope_of rfl
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,47,48] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals
      simp [function] at found
      subst b
      constructor
      · intro j stm present
        have cases : j = 0 ∨ j = 1 := by
          have bound := lt_of_getElem? present
          simp only [List.length_cons,List.length_nil] at bound
          omega
        rcases cases with rfl | rfl
        all_goals simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
          Option.some.injEq,reduceCtorEq] at present
        all_goals subst stm; intro x member; simp [Driver.instArgs] at member
        all_goals subst x; simp [availOf,function,defsBefore,defsFrom]
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member <;>
          subst x <;> simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 ∨ x = 48 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl | rfl
    all_goals try (change y ∈ ([] : List Nat) at member; cases member)
    change y ∈ [47,47] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst y
    have bound : tl < 3 := by simpa [function] using fixed.2.1
    have choices : tl = 0 ∨ tl = 1 ∨ tl = 2 := by omega
    rcases choices with rfl | rfl | rfl <;> simp [parsOf,function]

/-- Complete original-scope source execution with empty outgoing arguments and
a reachable trapping scalar successor body; actual lowering is checked by the kernel. -/
theorem driver_witness : ∃ result,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial,[],Clif.Mem.empty⟩ =
      .trapped .intDivz := by
  have success := lower_success
  cases run : Stock.lower function with
  | error message => rw [run] at success; cases success
  | ok result => exact ⟨result,rfl,scope,dominated,rfl,rfl⟩

end Backend.Stock.Proof.ConditionalValues.EmptyTrapFixture
