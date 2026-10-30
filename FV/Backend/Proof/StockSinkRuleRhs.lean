import FV.Backend.Proof.StockRuleFrame
import FV.Backend.Proof.StockPolicy
import FV.Arm.MinTheory
import FV.Backend.Proof.IselInterp

/-! State frames across the direct sink binding in generated rule RHSs. -/
namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- A direct sink call changes only its own sunk bit, including when evaluation
returns `none`. The environment binding and target inequality are explicit here;
the matched-rule composition must derive them from the actual load pattern. -/
theorem sink_expr_other {ctx : Ctx} {st next : State}
    {env : Isle.Interp.Env V} {n k i j : Nat} {out : Option V}
    {tr tr' : Array RuleId}
    (bound : env[k]? = some (some (.inst j))) (different : i ≠ j)
    (run : (evalExpr program (Stock.sem ctx) {} n
      (.term 13 236 [.var 18 k]) env).run (st,tr) = .ok (out,next,tr')) :
    next.sunk[i]! = st.sunk[i]! := by
  cases n with
  | zero => rw [evalExpr.eq_1] at run; cases run
  | succ n =>
    cases n with
    | zero => simp only [evalExpr.eq_7, evalArgs.eq_1, isel_monad] at run; cases run
    | succ n =>
      cases n with
      | zero =>
        simp only [evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_1, isel_monad] at run
        cases run
      | succ n =>
        simp only [evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2, bound,
          evalArgs.eq_2, isel_monad, applyTerm.eq_2, data_program.t236,
          Stock.sem, T.sink_inst] at run
        cases call : Stock.externCtor ctx T.sink_inst [.inst j] st with
        | fail =>
          simp only [T.sink_inst] at call
          rw [call] at run
          simp only [isel_monad] at run
          cases run
        | unmodeled reason =>
          simp only [T.sink_inst] at call
          rw [call] at run
          simp only [isel_monad] at run
          cases run
        | ok pair =>
          obtain ⟨value, middle⟩ := pair
          have state := (sink_accepted call).2.2.2.2
          simp only [T.sink_inst] at call
          rw [call] at run
          simp only [isel_monad, Except.ok.injEq, Prod.mk.injEq] at run
          obtain ⟨_, rfl, _⟩ := run
          rw [state]
          simp [getElem!_def, Array.getElem?_setIfInBounds, different, Ne.symm different]

/-- The whole RHS preserves another slot, including every instruction emitted
after the leading sink and every successful partial-result path. Only smaller
interpreter executions are used, so this closes an inductive rule contract. -/
theorem sink_let_other {ctx : Ctx} {st next : State}
    {blocked : Term → Bool} {env : Isle.Interp.Env V} {n k x ty i j : Nat}
    {body : Expr} {out : Option V} {tr tr' : Array RuleId}
    (frames : ∀ m, m < n → CtorFreeAt program (Stock.sem ctx) {} blocked
      (fun a b => b.sunk[i]! = a.sunk[i]!) m)
    (bound : env[k]? = some (some (.inst j))) (different : i ≠ j)
    (free : exprCtorFree program blocked body = true)
    (run : (evalExpr program (Stock.sem ctx) {} n
      (.let ty [(x,13,.term 13 236 [.var 18 k])] body) env).run (st,tr) =
        .ok (out,next,tr')) : next.sunk[i]! = st.sunk[i]! := by
  cases n with
  | zero => rw [evalExpr.eq_1] at run; cases run
  | succ n =>
    rw [evalExpr.eq_6] at run
    obtain ⟨boundEnv, ⟨middle, trm⟩, bindsRun, bodyRun⟩ := bind_ok run
    have bindFrame : middle.sunk[i]! = st.sunk[i]! := by
      cases n with
      | zero => rw [evalBinds.eq_1] at bindsRun; cases bindsRun
      | succ m =>
        rw [evalBinds.eq_3] at bindsRun
        obtain ⟨value, ⟨sunk, trs⟩, sinkRun, restRun⟩ := bind_ok bindsRun
        have first := sink_expr_other bound different sinkRun
        cases value with
        | none => cases pure_ok restRun; exact first
        | some value =>
          simp only at restRun
          split at restRun
          · have rest := (frames m (by omega)).binds _ _ _ _ _ _ _ (by rfl) restRun
            exact rest.trans first
          · exact (throw_ok restRun).elim
    cases boundEnv with
    | none => cases pure_ok bodyRun; exact bindFrame
    | some bodyEnv =>
      exact ((frames n (Nat.lt_succ_self n)).expr _ _ _ _ _ _ _ free bodyRun).trans bindFrame

end Backend.Stock.Proof.SinkRules
