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
      exact ⟨value,inst,available,called,same,trace,binding⟩

end Backend.Stock.Proof.Acquire810
