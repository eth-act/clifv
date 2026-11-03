import FV.Backend.Proof.StockAcquireReadPendingMarks
import FV.Backend.Proof.StockSinkRuleSyntax

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- Empty interpreter work supplies the empty original read frontier. -/
theorem ReadPendingExecution.refl (ctx : Ctx) (state : State) : ReadPendingExecution ctx state state :=
  ⟨[],.nil state⟩

/-- Interpreter composition retains the complete general pending list. -/
theorem ReadPendingExecution.trans {ctx : Ctx} {before middle after : State}
    (first : ReadPendingExecution ctx before middle) (second : ReadPendingExecution ctx middle after) :
    ReadPendingExecution ctx before after := by
  obtain ⟨left,first⟩ := first
  obtain ⟨right,second⟩ := second
  exact ⟨left++right,first.append second⟩

/-- Non-sink constructors preserve the source frontier and its complete mark fields. -/
theorem stock_ctor_free_read_frame {ctx : Ctx} {term : Term} {args : List V}
    {before after : State} {out : V}
    (free : SinkRules.blocked term = false)
    (run : Stock.externCtor ctx term args before = .ok (out,after)) : ReadPendingExecution ctx before after := by
  have different : term.id ≠ TId.sink_inst := by simpa [SinkRules.blocked] using free
  have shape : ¬ (term.id = TId.sink_inst ∧ ∃ producer,args = [.inst producer]) :=
    fun actual => different actual.1
  exact ⟨[],.frame (stock_ctor_entryColor run) (stock_ctor_color_without_sink shape run)
    (stock_ctor_sunk_without_sink_shape shape run) (.nil after)⟩

/-- Both pattern-based helper matches derive their bound original source memory frame. -/
theorem pattern_sink_read_target {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {before after : State} {trace afterTrace : Array RuleId} {bound : Isle.Interp.Env V}
    {fuel : Nat} {args : List V} (atomic : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if atomic then rule_inst_3905 else rule_inst_4203) args).run (before,trace) =
        .ok (some bound,after,afterTrace)) :
    ∃ producer,bound[if atomic then 1 else 3]? = some (some (.inst producer)) ∧ SourceReadFrame ctx producer := by
  obtain ⟨producer,info,fields,state,traceEq,installed,format,binding⟩ := SinkRules.pattern_sink_target atomic run
  have kinds : (if atomic then 17 else 16) = 16 ∨ (if atomic then 17 else 16) = 17 := by cases atomic <;> simp
  refine ⟨producer,binding,?_⟩
  intro env p before after executed
  exact sink_format_source_step_memory sources installed kinds format executed

/-- Both eligibility-based root matches derive the same original ordinary-load memory frame. -/
theorem eligibility_sink_read_target {f : Clif.Function} {ctx : Ctx} (sources : SinkFormatSources f ctx)
    {before after : State} {trace afterTrace : Array RuleId} {bound : Isle.Interp.Env V}
    {fuel : Nat} {args : List V} (signed : Bool)
    (run : (matchRule program (Stock.sem ctx) {} fuel
      (if signed then rule_lower_1359 else rule_lower_1300) args).run (before,trace) =
        .ok (some bound,after,afterTrace)) :
    ∃ producer,bound[5]? = some (some (.inst producer)) ∧ SourceReadFrame ctx producer := by
  obtain ⟨original,producer,info,fields,state,traceEq,defined,installed,data,binding⟩ := deferred_load_rule_source signed run
  have decoded : (Backend.sem ctx).unData 152 info.data = some (16,fields) := by rw [data]; rfl
  refine ⟨producer,binding,?_⟩
  intro env p before after executed
  exact sink_format_source_step_memory sources installed (Or.inl rfl) decoded executed

end Backend.Stock.Proof.Acquire810
