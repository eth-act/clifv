import FV.Backend.Proof.StockAcquireSinkFormatDriver
import FV.Backend.Proof.StockSinkTargetBinding

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

/-- Actual helper matches derive their original source and successful memory frame internally. -/
theorem stock_lower_pattern_sink_source_memory {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList)
    {before matched : State} {trace matchedTrace : Array RuleId} {bound : Isle.Interp.Env V}
    {fuel : Nat} {args : List V} (atomic : Bool)
    (matchedRun : (matchRule program (Stock.sem event.ctx) {} fuel
      (if atomic then rule_inst_3905 else rule_inst_4203) args).run (before,trace) =
        .ok (some bound,matched,matchedTrace)) :
    ∃ (producer : Nat) (info : IInfo) (inst : Clif.Inst),
      matched = before ∧ matchedTrace = trace ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some inst ∧ instData f inst = .ok info.data ∧
      bound[if atomic then 1 else 3]? = some (some (.inst producer)) ∧
      ∀ (env : Clif.Env) (p : Clif.Program) (source next : Clif.Frame × Clif.Mem),
        SourceInstResult env p event.ctx producer source next → next.2 = source.2 := by
  obtain ⟨producer,info,fields,state,traceEq,installed,format,binding⟩ :=
    SinkRules.pattern_sink_target atomic matchedRun
  have kinds : (if atomic then 17 else 16) = 16 ∨ (if atomic then 17 else 16) = 17 := by
    cases atomic <;> simp
  obtain ⟨inst,source,encoded,sourceKinds⟩ :=
    stock_lower_sink_format_sources run event events producer info installed _ fields kinds format
  refine ⟨producer,info,inst,state,traceEq,installed,source,encoded,binding,?_⟩
  intro env p source next executed
  exact stock_lower_sink_format_source_memory run events installed kinds format executed

end Backend.Stock.Proof.Acquire810
