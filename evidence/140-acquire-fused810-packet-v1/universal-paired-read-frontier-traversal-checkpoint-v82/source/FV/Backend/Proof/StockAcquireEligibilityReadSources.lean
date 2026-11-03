import FV.Backend.Proof.StockAcquireDeferredLoadRootPattern

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

private theorem iflet_original_target {ctx : Ctx} {before after : State}
    {trace afterTrace : Array RuleId} {env bound : Isle.Interp.Env V} {fuel original producer : Nat}
    (binding : env[4]? = some (some (.value original))) (defined : ctx.defInst? original = some producer)
    (run : (matchIfLets program (Stock.sem ctx) {} fuel
      [⟨.bind 18 5 (.wildcard 18),.term 18 221 [.var 15 4]⟩] env).run (before,trace) =
        .ok (some bound,after,afterTrace)) :
    after = before ∧ afterTrace = trace ∧ bound[5]? = some (some (.inst producer)) := by
  match fuel with
  | 0 => rw [matchIfLets.eq_1] at run; cases run
  | 1 => simp only [matchIfLets.eq_3,evalExpr.eq_1,isel_monad] at run; cases run
  | 2 => simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_1,isel_monad] at run; cases run
  | 3 => simp only [matchIfLets.eq_3,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_1,isel_monad] at run; cases run
  | n+4 =>
    obtain ⟨actual,eligible,state,traceEq,boundAt⟩ := stock_sink_iflet binding run
    have origin := stock_ctor_output_instructions eligible actual (by simp [V.instsIn])
    have actualDefined : ctx.defInst? original = some actual := by
      rcases origin with impossible | ⟨value,member,definition⟩
      · simp [instsInL,V.instsIn] at impossible
      · have same : value = original := by simpa [valsInL,V.valsIn] using member
        subst value
        exact definition
    have same : actual = producer := Option.some.inj (actualDefined.symm.trans defined)
    subst actual
    exact ⟨state,traceEq,boundAt⟩

/-- Complete matching binds both extension-load sink targets to the original load definition. -/
theorem deferred_load_rule_source {ctx : Ctx} {before after : State}
    {trace afterTrace : Array RuleId} {bound : Isle.Interp.Env V} {fuel : Nat} {args : List V}
    (signed : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) args).run (before,trace) =
        .ok (some bound,after,afterTrace)) :
    ∃ (original producer : Nat) (info : IInfo) (fields : List V),
      after = before ∧ afterTrace = trace ∧ ctx.defInst? original = some producer ∧
      ctx.insts[producer]? = some info ∧ info.data = .data 152 16 fields ∧
      bound[5]? = some (some (.inst producer)) := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at run; cases run
  | succ fuel =>
    obtain ⟨env,argsRun,iflets⟩ := matchRule_some_inv run
    obtain ⟨original,producer,info,fields,binding,defined,installed,data⟩ := deferred_load_root_args signed argsRun
    have shape : (if signed then rule_lower_1359 else rule_lower_1300).iflets =
        [⟨.bind 18 5 (.wildcard 18),.term 18 221 [.var 15 4]⟩] := by cases signed <;> rfl
    rw [shape] at iflets
    obtain ⟨state,traceEq,boundAt⟩ := iflet_original_target binding defined iflets
    exact ⟨original,producer,info,fields,state,traceEq,defined,installed,data,boundAt⟩

/-- Actual extension-load matches derive their original successful source memory frame. -/
theorem stock_lower_eligibility_sink_source_memory {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    {before matched : State} {trace matchedTrace : Array RuleId} {bound : Isle.Interp.Env V}
    {fuel : Nat} {args : List V} (signed : Bool)
    (matchedRun : (matchRule program (Stock.sem event.ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) args).run (before,trace) =
        .ok (some bound,matched,matchedTrace)) :
    ∃ (producer : Nat) (info : IInfo) (inst : Clif.Inst),
      matched = before ∧ matchedTrace = trace ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some inst ∧ instData f inst = .ok info.data ∧ bound[5]? = some (some (.inst producer)) ∧
      ∀ (env : Clif.Env) (p : Clif.Program) (source next : Clif.Frame × Clif.Mem),
        SourceInstResult env p event.ctx producer source next → next.2 = source.2 := by
  obtain ⟨original,producer,info,fields,state,traceEq,defined,installed,data,binding⟩ :=
    deferred_load_rule_source signed matchedRun
  have decoded : (Backend.sem event.ctx).unData 152 info.data = some (16,fields) := by
    rw [data]
    rfl
  obtain ⟨inst,source,encoded,kinds⟩ :=
    stock_lower_sink_format_sources run event events producer info installed 16 fields (Or.inl rfl) decoded
  refine ⟨producer,info,inst,state,traceEq,installed,source,encoded,binding,?_⟩
  intro env p source next executed
  exact stock_lower_sink_format_source_memory run events installed (Or.inl rfl) decoded executed

end Backend.Stock.Proof.Acquire810
