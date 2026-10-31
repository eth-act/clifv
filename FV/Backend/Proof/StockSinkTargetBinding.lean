import FV.Backend.Proof.StockPatternSink

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem data_input {ctx : Ctx} {st : State} {v : V} {fields : List V}
    (run : (Stock.sem ctx).extract T.inst_data_value v st = .ok fields) :
    ∃ i,v = .inst i := by
  cases v with
  | inst i => exact ⟨i,rfl⟩
  | _ => cases run

private theorem pattern_target {ctx : Ctx} {st : State} {v : V} {k ft fmt : Nat}
    {rest : List Pattern} {env bound : Isle.Interp.Env V} {term : Term}
    (lookup : termOf program ft = .ok term) (kind : term.kind = .enumVariant fmt)
    (run : matchPat program (Stock.sem ctx) st
      (.bind 18 k (.term 18 209 [.wildcard 14,.term 152 ft rest])) v env = .ok (some bound)) :
    ∃ i info fields,v = .inst i ∧ ctx.insts[i]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (fmt,fields) := by
  obtain ⟨_,inner⟩ := matchPat_bind_inv run
  obtain ⟨values,extracted,args⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl inner
  obtain ⟨i,rfl⟩ := data_input extracted
  change (match ctx.insts[i]? with
    | some info => ExtResult.ok [V.ty (info.resTys.head?.getD .invalid),info.data]
    | none => ExtResult.unmodeled s!"inst {i}") = .ok values at extracted
  cases found : ctx.insts[i]? with
  | none => rw [found] at extracted; cases extracted
  | some info =>
    rw [found] at extracted
    cases extracted
    obtain ⟨env1,_,tail⟩ := matchArgs_cons_inv args
    obtain ⟨env2,data,_⟩ := matchArgs_cons_inv tail
    obtain ⟨fields,decoded,_⟩ := matchPat_enum_inv lookup kind data
    exact ⟨i,info,fields,rfl,found,decoded⟩

private theorem empty_iflets {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {fuel : Nat} {rule : Rule} {vs : List V}
    (empty : rule.iflets = [])
    (run : (matchRule program (Stock.sem ctx) {} fuel rule vs).run (st,tr) =
      .ok (some bound,matched,tr')) :
    matched = st ∧ tr' = tr ∧
      matchArgs program (Stock.sem ctx) st rule.args vs
        (Array.replicate rule.vars.length none) = .ok (some bound) := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at run; cases run
  | succ fuel =>
    obtain ⟨env,args,ifs⟩ := matchRule_some_inv run
    rw [empty] at ifs
    cases fuel with
    | zero => rw [matchIfLets.eq_1] at ifs; cases ifs
    | succ fuel =>
      rw [matchIfLets.eq_2] at ifs
      cases ifs
      exact ⟨rfl,rfl,args⟩

/-- Complete matching derives the actual load target for arbitrary helper inputs.
The first argument of the ordinary-load helper need not be supplied as a typed value. -/
theorem pattern_sink_target {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {fuel : Nat} {vs : List V}
    (atomic : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if atomic then rule_inst_3905 else rule_inst_4203) vs).run (st,tr) =
        .ok (some bound,matched,tr')) :
    ∃ i info fields,matched = st ∧ tr' = tr ∧ ctx.insts[i]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (if atomic then 17 else 16,fields) ∧
      bound[if atomic then 1 else 3]? = some (some (.inst i)) := by
  obtain ⟨state,trace,args⟩ := empty_iflets (by cases atomic <;> rfl) run
  cases atomic with
  | true =>
    simp only [↓reduceIte,rule_inst_3905] at args
    cases vs with
    | nil => cases args
    | cons v tail =>
      obtain ⟨env1,head,rest⟩ := matchArgs_cons_inv args
      cases tail with
      | cons value values => cases rest
      | nil =>
        simp only [matchArgs,pure,Except.pure] at rest
        cases rest
        obtain ⟨i,info,fields,rfl,found,format⟩ := pattern_target data_program.t2464 rfl head
        obtain ⟨inside,inner⟩ := matchPat_bind_inv head
        have binding := stock_pattern_keeps (k := 1) (by decide) inner
        exact ⟨i,info,fields,state,trace,found,format,binding.trans (by rfl)⟩
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,rule_inst_4203] at args
    cases vs with
    | nil => cases args
    | cons ty tail =>
      obtain ⟨env1,_,rest⟩ := matchArgs_cons_inv args
      cases tail with
      | nil => cases rest
      | cons v tail =>
        obtain ⟨env2,head,rest⟩ := matchArgs_cons_inv rest
        cases tail with
        | cons value values => cases rest
        | nil =>
          simp only [matchArgs,pure,Except.pure] at rest
          cases rest
          obtain ⟨i,info,fields,rfl,found,format⟩ := pattern_target data_program.t2463 rfl head
          obtain ⟨inside,inner⟩ := matchPat_bind_inv head
          have binding := stock_pattern_keeps (k := 3) (by decide) inner
          exact ⟨i,info,fields,state,trace,found,format,binding.trans (by simp [inside])⟩

/-- Both installed helpers inhabit the arbitrary-input target contract. -/
theorem pattern_sink_target_witness (atomic : Bool) :
    ∃ (ctx : Ctx) (bound : Isle.Interp.Env V) (matched : State) (trace : Array RuleId)
      (i : Nat) (info : IInfo) (fields : List V),
      (matchRule program (Stock.sem ctx) {} 2
        (if atomic then rule_inst_3905 else rule_inst_4203)
        (if atomic then [.inst 0] else [.ty (.int 8),.inst 0])).run (sinkState,#[]) =
          .ok (some bound,matched,trace) ∧
      matched = sinkState ∧ trace = #[] ∧ ctx.insts[i]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (if atomic then 17 else 16,fields) ∧
      bound[if atomic then 1 else 3]? = some (some (.inst i)) := by
  obtain ⟨bound,matched,trace,_,_,run,_,_⟩ := stock_loadSink_pattern_witness atomic
  obtain ⟨i,info,fields,state,tr,found,format,binding⟩ := pattern_sink_target atomic run
  exact ⟨_,bound,matched,trace,i,info,fields,run,state,tr,found,format,binding⟩

end Backend.Stock.Proof.SinkRules
