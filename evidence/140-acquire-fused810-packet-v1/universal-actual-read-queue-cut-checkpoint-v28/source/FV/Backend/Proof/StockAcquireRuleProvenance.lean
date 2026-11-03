import FV.Backend.Proof.StockAcquireMatchSource
import FV.Backend.Proof.StockAcquireRhsReceipts

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- The complete actual root810 match and RHS derive the unique deferred source and its sink update.
Every premise is an actual evaluator receipt. No source acceptance condition changes. -/
theorem acquire_rule_sink_provenance {ctx : Ctx} {st matched next : State}
    {before matchedTrace after : Array RuleId} {bound : Isle.Interp.Env V} {m n ii : Nat} {out : V}
    (matchedRun : (matchRule program (Stock.sem ctx) {} (m+5) rule_lower_1272 [.inst ii]).run
      (st,before) = .ok (some bound,matched,matchedTrace))
    (evaluatedRun : (evalExpr program (Stock.sem ctx) {} (n+20) rule_lower_1272.rhs bound).run
      (matched,matchedTrace) = .ok (some out,next,after)) :
    ∃ value producer sunk info fields,
      ctx.defInst? value = some producer ∧ st.uses[value]! = .once ∧
      ctx.insts[producer]!.results.length = 1 ∧ st.entryColor[producer]! ≠ 0 ∧
      st.color = some (st.entryColor[producer]!+1) ∧
      Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,sunk) ∧
      sunk = {st with color := some st.entryColor[producer]!,sunk := st.sunk.set! producer true} ∧
      ctx.insts[producer]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (17,fields) := by
  obtain ⟨env,value,producer,args,held,source,same,trace,binding⟩ := acquire_root_match_source matchedRun
  subst matched
  subst matchedTrace
  obtain ⟨ty,flags,typeValue,flagValue⟩ := AcquireHelpers.acquire_rhs_inputs evaluatedRun
  obtain ⟨result,middle,middleTrace,called⟩ :=
    AcquireHelpers.acquire_rhs_sink_execution typeValue flagValue binding evaluatedRun
  obtain ⟨sunk,info,fields,sink,frame,installed,format⟩ :=
    AcquireHelpers.sink_atomic_call_receipt (by omega) called
  have eligible : Stock.externCtor ctx T.is_sinkable_inst [.value value] st = .ok (.inst producer,st) := by
    change (match Stock.source ctx st value with
      | some (i,true) => ExtResult.ok (V.inst i,st)
      | _ => ExtResult.fail) = _
    rw [source]
  have provenance := stock_sink_resultful eligible sink
  have accepted := sink_accepted sink
  exact ⟨value,producer,sunk,info,fields,provenance.2.1,provenance.2.2.1,
    provenance.2.2.2.1,accepted.1,accepted.2.1,sink,frame,installed,format⟩

end Backend.Stock.Proof.Acquire810
