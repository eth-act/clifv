import FV.Backend.Proof.StockAcquireReadPendingRhs

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- Complete pattern-helper rules derive original read frontiers through all successful RHS paths. -/
theorem pattern_sink_rule_read_pending {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {before matched after : State} {trace matchedTrace afterTrace : Array RuleId}
    {bound : Isle.Interp.Env V} {n fuel : Nat} {args : List V} {out : Option V}
    (frames : ∀ m,m < n → CtorFreeAt program (Stock.sem ctx) {} SinkRules.blocked (ReadPendingExecution ctx) m)
    (atomic : Bool)
    (matchedRun : (matchRule program (Stock.sem ctx) {} fuel
      (if atomic then rule_inst_3905 else rule_inst_4203) args).run (before,trace) =
        .ok (some bound,matched,matchedTrace))
    (rhsRun : (evalExpr program (Stock.sem ctx) {} n
      (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched,matchedTrace) =
        .ok (out,after,afterTrace)) : ReadPendingExecution ctx matched after := by
  obtain ⟨producer,binding,source⟩ := pattern_sink_read_target sources atomic matchedRun
  have guards : termCtorFree program SinkRules.blocked = (fun t => t != 236) := funext SinkRules.term_guard
  cases atomic with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,rule_inst_4203] at rhsRun binding
    apply sink_let_read_pending frames binding source ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel
  | true =>
    simp only [↓reduceIte,rule_inst_3905] at rhsRun binding
    apply sink_let_read_pending frames binding source ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel

/-- Complete extension-load rules derive the same frontier from their real eligibility match. -/
theorem eligibility_sink_rule_read_pending {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {before matched after : State} {trace matchedTrace afterTrace : Array RuleId}
    {bound : Isle.Interp.Env V} {n fuel : Nat} {args : List V} {out : Option V}
    (frames : ∀ m,m < n → CtorFreeAt program (Stock.sem ctx) {} SinkRules.blocked (ReadPendingExecution ctx) m)
    (signed : Bool)
    (matchedRun : (matchRule program (Stock.sem ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) args).run (before,trace) =
        .ok (some bound,matched,matchedTrace))
    (rhsRun : (evalExpr program (Stock.sem ctx) {} n
      (if signed then rule_lower_1359 else rule_lower_1300).rhs bound).run (matched,matchedTrace) =
        .ok (out,after,afterTrace)) : ReadPendingExecution ctx matched after := by
  obtain ⟨producer,binding,source⟩ := eligibility_sink_read_target sources signed matchedRun
  have guards : termCtorFree program SinkRules.blocked = (fun t => t != 236) := funext SinkRules.term_guard
  cases signed with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,rule_lower_1300] at rhsRun
    apply sink_let_read_pending frames binding source ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel
  | true =>
    simp only [↓reduceIte,rule_lower_1359] at rhsRun
    apply sink_let_read_pending frames binding source ?_ rhsRun
    rw [exprCtorFree,guards]
    decide +kernel

/-- The real generated interpreter derives complete pending-read classification, including nested helper calls. -/
theorem read_pending_interpreter_frames {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx) :
    ∀ n,CtorFreeAt program (Stock.sem ctx) {} SinkRules.blocked (ReadPendingExecution ctx) n := by
  apply ctorFreeAt_inductive (p := program) (sem := Stock.sem ctx) (cfg := {})
    (blocked := SinkRules.blocked) (R := ReadPendingExecution ctx)
    (ReadPendingExecution.refl ctx) (fun _ _ _ => ReadPendingExecution.trans)
    (fun _ _ _ _ _ => stock_ctor_free_read_frame) rfl (special := SinkRules.Exceptional)
  · intro term rule member
    exact SinkRules.rule_cases member
  · intro n frames rule special fuel args bound before trace matched matchedTrace out after afterTrace matchedRun rhsRun
    rcases special with rfl | rfl | rfl | rfl
    · obtain ⟨producer,info,fields,same,rest⟩ := SinkRules.pattern_sink_target true matchedRun
      have completed : ReadPendingExecution ctx matched after :=
        pattern_sink_rule_read_pending sources frames true matchedRun rhsRun
      simpa only [same] using completed
    · obtain ⟨producer,info,fields,same,rest⟩ := SinkRules.pattern_sink_target false matchedRun
      have completed : ReadPendingExecution ctx matched after :=
        pattern_sink_rule_read_pending sources frames false matchedRun rhsRun
      simpa only [same] using completed
    · obtain ⟨original,producer,info,fields,same,rest⟩ := deferred_load_rule_source false matchedRun
      have completed : ReadPendingExecution ctx matched after :=
        eligibility_sink_rule_read_pending sources frames false matchedRun rhsRun
      simpa only [same] using completed
    · obtain ⟨original,producer,info,fields,same,rest⟩ := deferred_load_rule_source true matchedRun
      have completed : ReadPendingExecution ctx matched after :=
        eligibility_sink_rule_read_pending sources frames true matchedRun rhsRun
      simpa only [same] using completed

end Backend.Stock.Proof.Acquire810
