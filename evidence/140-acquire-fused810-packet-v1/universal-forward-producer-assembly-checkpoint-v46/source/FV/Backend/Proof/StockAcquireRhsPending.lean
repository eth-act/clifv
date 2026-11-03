import FV.Backend.Proof.StockAcquireSinkCallPending
import FV.Backend.Proof.StockAcquireRhsOutput
import FV.Backend.Proof.StockAcquireSelectedPending

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- The actual root RHS defers exactly its bound producer and retains its real sink update.
Other pending loads remain represented by their unchanged prior sink bits. -/
theorem acquire_rhs_pending {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {env : Isle.Interp.Env V} {n producer : Nat} {out : V}
    (producerValue : env[4]? = some (some (.inst producer)))
    (run : (evalExpr program (Stock.sem ctx) {} (n+100) rule_lower_1272.rhs env).run
      (st,before) = .ok (some out,next,after)) :
    ∃ middle,Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) ∧
      PendingSinks ctx st [producer] next ∧
      next.sunk = st.sunk.set! producer true ∧ next.color = some st.entryColor[producer]! := by
  obtain ⟨ty,flags,typeValue,flagValue⟩ := AcquireHelpers.acquire_rhs_inputs (n := n+80) run
  obtain ⟨address,sunk,sinkTrace,instruction,sinkCall,decoded,output,state,fresh⟩ :=
    AcquireHelpers.acquire_rhs_output typeValue flagValue producerValue run
  obtain ⟨middle,sinkUnit,actual,sunkEq⟩ := sink_atomic_call_pending (fuel := n+92) (by omega) sinkCall
  have accepted := sink_accepted sinkUnit
  have entries : next.entryColor = sunk.entryColor := by rw [state]
  have color : next.color = sunk.color := by rw [state]
  have tail : PendingSinks ctx sunk [] next := .frame entries color (.nil next)
  refine ⟨middle,sinkUnit,?_,?_,?_⟩
  · simpa only [List.append_nil] using actual.append tail
  · rw [state]
    change sunk.sunk = _
    rw [sunkEq,accepted.2.2.2.2]
  · rw [state]
    change sunk.color = _
    obtain ⟨final,finalColor⟩ := actual.finalColor accepted.2.1
    have distance := actual.color_distance finalColor
    have eq : st.entryColor[producer]!+1 = final+1 := Option.some.inj (accepted.2.1.symm.trans distance)
    have finalEq : final = st.entryColor[producer]! := by omega
    rwa [finalEq] at finalColor

end Backend.Stock.Proof.Acquire810
