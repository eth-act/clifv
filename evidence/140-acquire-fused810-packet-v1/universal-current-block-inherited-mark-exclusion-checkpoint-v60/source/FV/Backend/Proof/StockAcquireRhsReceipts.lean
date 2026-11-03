import FV.Backend.Proof.StockAcquireSinkReceipts

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Successful evaluation of the actual root RHS reaches its bound producer's atomic sink. -/
theorem acquire_rhs_sink_execution {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {env : Isle.Interp.Env V} {n producer : Nat} {ty flags out : V}
    (typeValue : env[1]? = some (some ty))
    (flagValue : env[2]? = some (some flags))
    (producerValue : env[4]? = some (some (.inst producer)))
    (run : (evalExpr program (Stock.sem ctx) {} (n+20) rule_lower_1272.rhs env).run (st,before) =
      .ok (some out,next,after)) :
    ∃ value sunk trace,ApplyInternal program (Stock.sem ctx) {} (n+12) 27 564 [.inst producer]
      (st,before) value (sunk,trace) := by
  simp only [rule_lower_1272,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,evalArgs.eq_2,
    typeValue,flagValue,producerValue,isel_monad] at run
  cases called : (applyTerm program (Stock.sem ctx) {} (n+13) 27 564 [.inst producer]).run (st,before) with
  | error message => rw [called] at run; cases run
  | ok result =>
    obtain ⟨value,sunk,trace⟩ := result
    cases value with
    | none => rw [called] at run; simp only [isel_monad] at run; cases run
    | some value => exact ⟨value,sunk,trace,called⟩

/-- Successful actual RHS evaluation derives its own type and flag environment values. -/
theorem acquire_rhs_inputs {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {env : Isle.Interp.Env V} {n : Nat} {out : V}
    (run : (evalExpr program (Stock.sem ctx) {} (n+20) rule_lower_1272.rhs env).run (st,before) =
      .ok (some out,next,after)) :
    ∃ ty flags,env[1]? = some (some ty) ∧ env[2]? = some (some flags) := by
  cases typeLookup : env[1]? with
  | none =>
    simp only [rule_lower_1272,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
      evalArgs.eq_2,typeLookup,isel_monad] at run
    cases run
  | some typeOption =>
    cases typeOption with
    | none =>
      simp only [rule_lower_1272,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
        evalArgs.eq_2,typeLookup,isel_monad] at run
      cases run
    | some ty =>
      cases flagLookup : env[2]? with
      | none =>
        simp only [rule_lower_1272,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
          evalArgs.eq_2,typeLookup,flagLookup,isel_monad] at run
        cases run
      | some flagOption =>
        cases flagOption with
        | none =>
          simp only [rule_lower_1272,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,
            evalArgs.eq_2,typeLookup,flagLookup,isel_monad] at run
          cases run
        | some flags => exact ⟨ty,flags,rfl,rfl⟩

end Backend.Stock.Proof.AcquireHelpers
