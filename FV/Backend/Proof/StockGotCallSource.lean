import FV.Backend.Proof.StockGotCallRhs
import FV.Backend.Proof.StockCallStaticSource
namespace Backend.Stock.Proof.GotCallFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open CallStaticFixture (count signature arguments callStatement calleeName)
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

def function (implicit : Bool) : Clif.Function := {CallStaticFixture.function false implicit with
  name := "stock_got_call_complete"
  externs := [(0,{name := calleeName,sig := signature false implicit,colocated := false})]}
private theorem source_dominated (implicit : Bool) : Dominated (function implicit) := by
  constructor
  · cases implicit <;> decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp only [function,CallStaticFixture.function,List.getElem?_cons_zero,Option.some.injEq] at found
      subst b
      constructor
      · intro j stm statement x member
        cases implicit
        all_goals rcases j with _ | (_ | j)
        all_goals simp [function,CallStaticFixture.function,callStatement] at statement
        all_goals subst stm
        all_goals simp [Driver.instArgs,arguments,count] at member
        all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [availOf,function,CallStaticFixture.function,callStatement,signature,arguments,count,defsBefore,defsFrom]
      · intro x member
        cases implicit
        all_goals simp [abiTerm,Driver.termArgs,function,CallStaticFixture.function,callStatement,signature,sretRet,sigRets,arguments,count] at member
        all_goals rcases member with rfl | rfl
        all_goals simp [availOf,function,CallStaticFixture.function,callStatement,signature,arguments,count,defsBefore,defsFrom]
    | succ bi => simp [function,CallStaticFixture.function] at found
  · intro ctx ranges st build tl x incoming notLocal y member
    have bound := (inFix_fixOk (f := function implicit) (ctx := ctx) (gn := id)).cand tl x incoming
    have length : (function implicit).blocks.length = 1 := rfl
    omega


/-- Both real GOT-call sources retain the original input conditions, including
nine direct-call arguments with stack traffic and an implicit sret source. -/
theorem source_conditions (implicit : Bool) : LowerScope (function implicit) ∧ Dominated (function implicit) ∧
    ArityOk (function implicit) ∧ AbiSigsOk (function implicit) := by
  have signatureOk := (CallStaticFixture.source_conditions false implicit).2.2.2
  constructor
  · cases implicit <;> apply lowerScope_of <;> decide +kernel
  constructor
  · exact source_dominated implicit
  constructor
  · cases implicit <;> apply arityOk_of <;> decide +kernel
  constructor
  · constructor
    · exact signatureOk
    · intro e member
      simp only [function,List.mem_singleton] at member
      subst e
      exact signatureOk
  · intro sig member
    cases implicit <;> simp [indSigs,function,CallStaticFixture.function,callStatement] at member
end Backend.Stock.Proof.GotCallFixture
