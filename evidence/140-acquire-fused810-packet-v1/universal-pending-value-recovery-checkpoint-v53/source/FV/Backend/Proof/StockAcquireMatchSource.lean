import FV.Backend.Proof.StockSinkProvenance

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Successful root810 eligibility derives its source value from the actual environment. -/
theorem acquire_iflet_source {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env bound : Isle.Interp.Env V} {n : Nat}
    (run : (matchIfLets program (Stock.sem ctx) {} (n+4)
      [⟨.bind 18 4 (.wildcard 18),.term 18 221 [.var 15 3]⟩] env).run (st,tr) =
        .ok (some bound,next,tr')) :
    ∃ value inst,env[3]? = some (some (.value value)) ∧
      Stock.externCtor ctx T.is_sinkable_inst [.value value] st = .ok (.inst inst,st) ∧
      next = st ∧ tr' = tr ∧ bound[4]? = some (some (.inst inst)) := by
  cases available : env[3]? with
  | none =>
    simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
      available,evalArgs.eq_2,isel_monad] at run
    cases run
  | some option =>
    cases option with
    | none =>
      simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
        available,evalArgs.eq_2,isel_monad] at run
      cases run
    | some value =>
      cases value <;> try (
        simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
          available,evalArgs.eq_2,isel_monad,applyTerm.eq_2,data_program.t221,
          T.is_sinkable_inst,Stock.sem,Stock.externCtor] at run
        cases run)
      rename_i value
      obtain ⟨inst,called,same,trace,binding⟩ := stock_sink_iflet available run
      exact ⟨value,inst,rfl,called,same,trace,binding⟩

/-- The actual root810 match derives its retained producer through the original eligibility call. -/
theorem acquire_root_match_source {ctx : Ctx} {st matched : State} {tr tr' : Array RuleId}
    {bound : Isle.Interp.Env V} {n ii : Nat}
    (run : (matchRule program (Stock.sem ctx) {} (n+5) rule_lower_1272 [.inst ii]).run (st,tr) =
      .ok (some bound,matched,tr')) :
    ∃ env value producer,
      matchArgs program (Stock.sem ctx) st rule_lower_1272.args [.inst ii]
        (Array.replicate rule_lower_1272.vars.length none) = .ok (some env) ∧
      env[3]? = some (some (.value value)) ∧
      Stock.source ctx st value = some (producer,true) ∧ matched = st ∧ tr' = tr ∧
      bound[4]? = some (some (.inst producer)) := by
  obtain ⟨env,args,iflets⟩ := matchRule_some_inv (m := n+4) run
  have actual : (matchIfLets program (Stock.sem ctx) {} (n+4)
      [⟨.bind 18 4 (.wildcard 18),.term 18 221 [.var 15 3]⟩] env).run (st,tr) =
        .ok (some bound,matched,tr') := by
    simpa only [rule_lower_1272] using iflets
  obtain ⟨value,producer,held,called,same,trace,binding⟩ := acquire_iflet_source actual
  have source : Stock.source ctx st value = some (producer,true) := by
    change (match Stock.source ctx st value with
      | some (i,true) => ExtResult.ok (V.inst i,st)
      | _ => ExtResult.fail) = ExtResult.ok (.inst producer,st) at called
    cases found : Stock.source ctx st value with
    | none => rw [found] at called; cases called
    | some pair =>
      obtain ⟨i,eligible⟩ := pair
      cases eligible with
      | false => rw [found] at called; cases called
      | true => rw [found] at called; cases called; rfl
  exact ⟨env,value,producer,args,held,source,same,trace,binding⟩

end Backend.Stock.Proof.Acquire810
