import FV.Backend.Proof.StockAcquireIfletEnvironment

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- The original SSA typing remains exact in every actual retained event context. -/
theorem stock_lower_event_result_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {slot m value : Nat} {info : IInfo} {inst : Clif.Inst} {ty : CTy}
    (installed : event.ctx.insts[slot]? = some info) (source : info.clif = some inst)
    (resultAt : info.results[m]? = some value) (typeAt : info.resTys[m]? = some ty) :
    event.ctx.valueType? value = some ty := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have originalSlot : original.insts[slot]? = some info := by
    rw [← view.insts]
    exact (stock_lower_record_context run scope events).2.2 slot info inst installed source
  have typed := (spec.facts.types dominated.ssa).1 slot info originalSlot m value ty resultAt typeAt
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
  simpa only [Ctx.valueType?,view.valTy] using typed

/-- Actual original atomic result typing supplies the acquire matcher's source type. -/
theorem stock_lower_acquire_source_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {producer value pointer : Nat} {info : IInfo} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (defined : event.ctx.defInst? value = some producer)
    (installed : event.ctx.insts[producer]? = some info)
    (source : info.clif = some (.atomicLoad ty flags pointer)) :
    event.ctx.valueType? value = some (CTy.ofClif ty) := by
  have mapped := (stock_lower_record_context run scope events).1
  have singleton := mapped_atomic_result_singleton mapped defined installed source
  obtain ⟨tys,types,resultTypes,length⟩ := mapped.resTys producer info _ installed source
  have tysEq : tys = [ty] := by simpa only [Clif.Inst.resultTypes,Option.some.injEq] using types.symm
  have typeAt : info.resTys[0]? = some (CTy.ofClif ty) := by
    rw [resultTypes,tysEq]
    rfl
  exact stock_lower_event_result_type run scope dominated events installed source
    (by rw [singleton];rfl) typeAt

end Backend.Stock.Proof.Acquire810
