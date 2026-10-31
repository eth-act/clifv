import FV.Backend.Proof.StockMemoryMixedStoreRecordSpec

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original instruction results retain their declared types in every actual scan context. -/
theorem stock_lower_source_result_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {i m x : Nat} {info : IInfo} {inst : Clif.Inst} {ty : CTy}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some inst)
    (resultAt : info.results[m]? = some x) (typeAt : info.resTys[m]? = some ty) :
    event.ctx.valueType? x = some ty := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,nodeBi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have types : event.ctx.valTy = original.valTy := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valTy
  have originalSource : original.insts[i]? = some info := by
    rw [← view.insts]
    exact globalSource
  simpa only [Ctx.valueType?,types] using
    (spec.facts.types dominated.ssa).1 i info originalSource m x ty resultAt typeAt

/-- A computed store value needs its original declared type, not parameter status. -/
theorem stock_mixed_store_record_spec_of_value_type (kind : Kind) (ty : Clif.Ty)
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j value pointer : Nat} {flags : Clif.MemFlags}
    (statement : b.body[j]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩)
    {pi : Nat} {pb : Clif.Block}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    {valueTy : CTy} (valueType : event.ctx.valueType? value = some valueTy)
    (width : kind.sourceOp = .store → valueTy = .int kind.width.bits) :
    Nonempty (RetainedStoreReturnSpec kind ty f result event b j value pointer flags) := by
  obtain ⟨term,record,body,step,split,member,current,unsunk,actual,records,recorded,emitted⟩ :=
    stock_lower_mixed_store_emitted run scope events block statement
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨valueReg,valueMapped⟩ := inv.typedReg value _ valueType
  obtain ⟨pointerReg,pointerMapped⟩ := inv.typedReg pointer _ (inv.addr64 _ _ _ pointer source clif rfl)
  have noDefinition := stock_lower_source_parameter_definition run dominated events pointerBlock parameter
  have typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits) := by
    intro plain
    rw [valueType,width plain]
  exact ⟨⟨term,record,body,step,info,valueReg,pointerReg,split,member,current,records,recorded,emitted,
    source,clif,typed,valueMapped,noDefinition,pointerMapped⟩⟩

end Backend.Stock.Memory.StoreRoots
