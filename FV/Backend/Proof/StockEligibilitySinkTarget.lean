import FV.Backend.Proof.StockProtectedSinkRules
import FV.Backend.Proof.StockCtorFlow
import FV.Backend.Proof.StockDFG

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem eligibility_ctor (ctx : Ctx) (st : State) (a : V) :
    Stock.externCtor ctx T.is_sinkable_inst [a] st =
      match a with
      | .value v => match source ctx st v with
        | some (i, true) => ExtResult.ok (V.inst i, st)
        | _ => ExtResult.fail
      | _ => ExtResult.fail := by
  cases a <;> rfl

private theorem iflet_value {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env bound : Isle.Interp.Env V} {x k n : Nat}
    (h : (matchIfLets program (Stock.sem ctx) {} (n + 4)
      [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩] env).run (st, tr) =
        .ok (some bound, next, tr')) :
    ∃ v, env[x]? = some (some (.value v)) := by
  simp only [matchIfLets.eq_3, evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2,
    evalArgs.eq_2, isel_monad] at h
  cases hv : env[x]? with
  | none => rw [hv] at h; simp only [isel_monad] at h; cases h
  | some value =>
    cases value with
    | none => rw [hv] at h; simp only [isel_monad] at h; cases h
    | some value =>
      cases hvv : value with
      | value v => exact ⟨v, rfl⟩
      | _ =>
        rw [hv] at h
        simp only [isel_monad, applyTerm.eq_2, data_program.t221,
          Stock.sem, isel_data, isel_monad] at h
        have hf : Stock.externCtor ctx T.is_sinkable_inst [value] st = .fail := by
          rw [eligibility_ctor, hvv]
        rw [hf] at h
        simp only [isel_monad] at h
        cases h


private theorem iflet_target {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {env bound : Isle.Interp.Env V} {fuel x k : Nat}
    (run : (matchIfLets program (Stock.sem ctx) {} fuel
      [⟨.bind 18 k (.wildcard 18),.term 18 221 [.var 15 x]⟩] env).run (st,tr) =
        .ok (some bound,matched,tr')) :
    ∃ v i,Stock.externCtor ctx T.is_sinkable_inst [.value v] st = .ok (.inst i,st) ∧
      matched = st ∧ tr' = tr ∧ bound[k]? = some (some (.inst i)) := by
  match fuel with
  | 0 => rw [matchIfLets.eq_1] at run; cases run
  | 1 => simp only [matchIfLets.eq_3,evalExpr.eq_1,isel_monad] at run; cases run
  | 2 => simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_1,isel_monad] at run; cases run
  | 3 => simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_1,isel_monad] at run; cases run
  | n+4 =>
    obtain ⟨v,value⟩ := iflet_value run
    obtain ⟨i,extracted,state,trace,binding⟩ := stock_sink_iflet value run
    exact ⟨v,i,extracted,state,trace,binding⟩

/-- Successful matching derives the actual source definition and sink binding. -/
theorem eligibility_sink_target {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {fuel : Nat} {vs : List V}
    (signed : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) vs).run (st,tr) =
        .ok (some bound,matched,tr')) :
    ∃ v i,matched = st ∧ tr' = tr ∧ ctx.defInst? v = some i ∧
      bound[5]? = some (some (.inst i)) := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at run; cases run
  | succ fuel =>
    obtain ⟨env,_,ifs⟩ := matchRule_some_inv run
    have shape : (if signed then rule_lower_1359 else rule_lower_1300).iflets =
        [⟨.bind 18 5 (.wildcard 18),.term 18 221 [.var 15 4]⟩] := by cases signed <;> rfl
    rw [shape] at ifs
    obtain ⟨v,i,extracted,state,trace,binding⟩ := iflet_target ifs
    have origin := stock_ctor_output_instructions extracted i (by simp [V.instsIn])
    have defined : ctx.defInst? v = some i := by
      rcases origin with impossible | ⟨x,member,definition⟩
      · simp [instsInL,V.instsIn] at impossible
      · have same : x = v := by simpa [valsInL,V.valsIn] using member
        subst x
        exact definition
    exact ⟨v,i,state,trace,defined,binding⟩

/-- An actual defining instruction cannot be a result-less protected slot. -/
theorem eligibility_sink_target_other {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {slot : Nat} (empty : ctx.insts[slot]!.results = []) {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {fuel : Nat} {vs : List V}
    (signed : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) vs).run (st,tr) =
        .ok (some bound,matched,tr')) :
    ∃ i,matched = st ∧ tr' = tr ∧ slot ≠ i ∧ bound[5]? = some (some (.inst i)) := by
  obtain ⟨v,i,state,trace,defined,binding⟩ := eligibility_sink_target signed run
  refine ⟨i,state,trace,?_,binding⟩
  intro same
  subst i
  obtain ⟨info,found,member⟩ := mapped.defInst v slot defined
  have nil : info.results = [] := by simpa only [getElem!_def,found,Option.getD_some] using empty
  simp [nil] at member

/-- Complete eligibility-rule execution preserves a result-less slot.
The original mapped context supplies the definition fact; no no-load family premise is needed. -/
theorem eligibility_sink_rule_frame {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {slot : Nat} (empty : ctx.insts[slot]!.results = []) {st matched next : State}
    {tr tr' tr'' : Array RuleId} {bound : Isle.Interp.Env V} {n fuel : Nat}
    {vs : List V} {out : Option V}
    (frames : ∀ m,m < n → CtorFreeAt program (Stock.sem ctx) {} blocked
      (fun a b => b.sunk[slot]! = a.sunk[slot]!) m)
    (signed : Bool)
    (matchedRun : (matchRule program (Stock.sem ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) vs).run (st,tr) =
        .ok (some bound,matched,tr'))
    (rhsRun : (evalExpr program (Stock.sem ctx) {} n
      (if signed then rule_lower_1359 else rule_lower_1300).rhs bound).run (matched,tr') =
        .ok (out,next,tr'')) : next.sunk[slot]! = st.sunk[slot]! := by
  obtain ⟨i,rfl,rfl,different,binding⟩ := eligibility_sink_target_other mapped empty signed matchedRun
  have guards : termCtorFree program blocked = (fun t => t != 236) := funext term_guard
  cases signed with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,rule_lower_1300] at rhsRun
    apply sink_let_other frames binding different ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel
  | true =>
    simp only [↓reduceIte,rule_lower_1359] at rhsRun
    apply sink_let_other frames binding different ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel

end Backend.Stock.Proof.SinkRules
