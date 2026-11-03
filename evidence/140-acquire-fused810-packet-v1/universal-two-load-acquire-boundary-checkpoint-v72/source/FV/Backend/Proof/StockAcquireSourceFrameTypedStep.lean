import FV.Backend.Proof.StockAcquireSourcePrefixChunkRun
import FV.Backend.Proof.LowerFrame
import FV.Backend.Proof.StockEntrySeed

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual indexed source steps preserve their original function. -/
theorem source_inst_result_function {ctx : Ctx} {slot : Nat} {env : Clif.Env} {program : Clif.Program}
    {before after : Clif.Frame × Clif.Mem} (step : SourceInstResult env program ctx slot before after) :
    after.1.func = before.1.func := by
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,updated,frame⟩ := step
  rw [frame]

/-- Original declared result types and real runtime outcomes preserve the complete frame typing relation. -/
theorem stock_lower_source_inst_frame_typed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {slot : Nat} {info : IInfo} {inst : Clif.Inst}
    (installed : event.ctx.insts[slot]? = some info) (source : info.clif = some inst) (nodup : info.results.Nodup)
    {env : Clif.Env} {program : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (function : before.1.func = f) (typed : FrameTyped event.ctx before.1)
    (step : SourceInstResult env program event.ctx slot before after) : FrameTyped event.ctx after.1 := by
  obtain ⟨actual,original,values,regs,rest,found,clif,body,evaluated,updated,frame⟩ := step
  have infoEq := Option.some.inj (found.symm.trans installed)
  subst actual
  have instEq := Option.some.inj (clif.symm.trans source)
  subst original
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨tys,resultShape,resultTypes,length⟩ := mapped.resTys slot info inst installed source
  have declared : inst.resultTypes (fun reference => (before.1.func.extern? reference).map (·.sig))
      (before.1.func.sigDecls.lookup ·) = some tys := by rw [function];exact resultShape
  have valuesTyped := instOutcome_types evaluated declared
  intro value ty actualValue valueType afterFound
  have foundValue : regs value = some actualValue := by simpa only [frame] using afterFound
  by_cases member : value ∈ info.results
  · obtain ⟨index,boundValue,resultAt,valueAt,bound⟩ := setMany_mem updated nodup value member
    have originalType : tys[index]? = some boundValue.ty := by
      have indexed := congrArg (fun list => list[index]?) valuesTyped
      simpa only [List.getElem?_map,valueAt,Option.map_some] using indexed.symm
    have typeAt : info.resTys[index]? = some (CTy.ofClif boundValue.ty) := by
      rw [resultTypes,List.getElem?_map,originalType]
      rfl
    have contextType := stock_lower_event_result_type run scope dominated events installed source resultAt typeAt
    have sameType := Option.some.inj (contextType.symm.trans valueType)
    have sameValue := Option.some.inj (bound.symm.trans foundValue)
    simpa only [sameValue] using sameType
  · have oldFound : before.1.regs value = some actualValue := (setMany_other updated member).symm.trans foundValue
    exact typed value ty actualValue valueType oldFound

end Backend.Stock.Proof.Acquire810
