import FV.Backend.Proof.StockAcquireReadPendingCtor

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- A direct sink expression adds precisely its matched original read to the pending trace. -/
theorem sink_expr_read_pending {ctx : Ctx} {before after : State}
    {env : Isle.Interp.Env V} {n key producer : Nat} {out : Option V} {trace afterTrace : Array RuleId}
    (bound : env[key]? = some (some (.inst producer))) (source : SourceReadFrame ctx producer)
    (run : (evalExpr program (Stock.sem ctx) {} n
      (.term 13 236 [.var 18 key]) env).run (before,trace) = .ok (out,after,afterTrace)) :
    ReadPendingExecution ctx before after := by
  cases n with
  | zero => rw [evalExpr.eq_1] at run; cases run
  | succ n =>
    cases n with
    | zero => simp only [evalExpr.eq_7,evalArgs.eq_1,isel_monad] at run; cases run
    | succ n =>
      cases n with
      | zero => simp only [evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_1,isel_monad] at run; cases run
      | succ n =>
        simp only [evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,bound,evalArgs.eq_2,
          isel_monad,applyTerm.eq_2,data_program.t236,Stock.sem,T.sink_inst] at run
        cases call : Stock.externCtor ctx T.sink_inst [.inst producer] before with
        | fail =>
          simp only [T.sink_inst] at call
          rw [call] at run
          simp only [isel_monad] at run
          cases run
        | unmodeled message =>
          simp only [T.sink_inst] at call
          rw [call] at run
          simp only [isel_monad] at run
          cases run
        | ok pair =>
          obtain ⟨value,middle⟩ := pair
          have output := (sink_accepted call).2.2.2.1
          subst value
          have actual := call
          simp only [T.sink_inst] at call
          rw [call] at run
          simp only [isel_monad,Except.ok.injEq,Prod.mk.injEq] at run
          obtain ⟨_,rfl,_⟩ := run
          exact ⟨[producer],.sink actual source (.nil middle)⟩

/-- Complete sink RHS evaluation retains the matched read and all recursively derived read frontiers. -/
theorem sink_let_read_pending {ctx : Ctx} {before after : State}
    {env : Isle.Interp.Env V} {n key localVar ty producer : Nat} {body : Expr}
    {out : Option V} {trace afterTrace : Array RuleId}
    (frames : ∀ m,m < n → CtorFreeAt program (Stock.sem ctx) {} SinkRules.blocked (ReadPendingExecution ctx) m)
    (bound : env[key]? = some (some (.inst producer))) (source : SourceReadFrame ctx producer)
    (free : exprCtorFree program SinkRules.blocked body = true)
    (run : (evalExpr program (Stock.sem ctx) {} n
      (.let ty [(localVar,13,.term 13 236 [.var 18 key])] body) env).run (before,trace) =
        .ok (out,after,afterTrace)) : ReadPendingExecution ctx before after := by
  cases n with
  | zero => rw [evalExpr.eq_1] at run; cases run
  | succ n =>
    rw [evalExpr.eq_6] at run
    obtain ⟨boundEnv,⟨middle,middleTrace⟩,bindsRun,bodyRun⟩ := bind_ok run
    have bindRead : ReadPendingExecution ctx before middle := by
      cases n with
      | zero => rw [evalBinds.eq_1] at bindsRun; cases bindsRun
      | succ m =>
        rw [evalBinds.eq_3] at bindsRun
        obtain ⟨value,⟨sunk,sunkTrace⟩,sinkRun,restRun⟩ := bind_ok bindsRun
        have first := sink_expr_read_pending bound source sinkRun
        cases value with
        | none => cases pure_ok restRun; exact first
        | some value =>
          simp only at restRun
          split at restRun
          · have rest := (frames m (by omega)).binds _ _ _ _ _ _ _ (by rfl) restRun
            exact first.trans rest
          · exact (throw_ok restRun).elim
    cases boundEnv with
    | none => cases pure_ok bodyRun; exact bindRead
    | some bodyEnv =>
      exact bindRead.trans ((frames n (Nat.lt_succ_self n)).expr _ _ _ _ _ _ _ free bodyRun)

end Backend.Stock.Proof.Acquire810
