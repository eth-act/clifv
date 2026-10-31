import FV.Backend.Proof.StockStoreRetention
import FV.Backend.Proof.StockMemoryReturnSpec
import FV.Backend.Proof.StockMemoryStoreMatch

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original parameter declarations determine types in the actual scan context. -/
theorem stock_lower_source_parameter_type {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) {x : Nat} {ty : Clif.Ty}
    (parameter : (x,ty) ∈ b.params) : event.ctx.valueType? x = some (CTy.ofClif ty) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,nodeBi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have types : event.ctx.valTy = original.valTy := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valTy
  simpa only [Ctx.valueType?,types] using
    (spec.facts.types dominated.ssa).2 b (List.mem_of_getElem? block) (x,ty) parameter

/-- Actual store data for composition comes from original syntax and the complete driver. -/
structure SingleStoreReturnSpec (kind : Kind) (ty : Clif.Ty) (f : Clif.Function) (result : Result)
    (event : BlockScanEvent) (b : Clif.Block) (value pointer : Nat) (flags : Clif.MemFlags) where
  term : ScanRecord
  record : ScanRecord
  body : BlockScan
  step : Step
  info : IInfo
  valueReg : Nat
  pointerReg : Nat
  split : SourceBodySplit f event b term body
  bodyRecords : body.records = [record]
  current : record.inst = blockStart f event.block+0
  records : record ∈ event.output.records
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0)
  typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits)
  valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int)
  parameter : event.ctx.defInst? pointer = none
  pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int)

/-- Store retention and operand mappings are internal consequences of original source syntax. -/
theorem stock_single_store_return_spec (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {value pointer : Nat} {flags : Clif.MemFlags}
    (singleton : b.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩]) (ret : b.term = .ret [])
    {pi vi : Nat} {pb vb : Clif.Block} {valueTy : Clif.Ty}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
    Nonempty (SingleStoreReturnSpec kind ty f result event b value pointer flags) := by
  have statement : b.body[0]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by simp [singleton]
  obtain ⟨term,record,body,step,split,member,current,unsunk,actual,records,recorded,emitted⟩ :=
    stock_lower_store_emitted run scope formats events block statement ret
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have inv := (stock_lower_record_context run scope events).1
  have valueType := stock_lower_source_parameter_type run dominated events valueBlock valueParameter
  obtain ⟨valueReg,valueMapped⟩ := inv.typedReg value _ valueType
  obtain ⟨pointerReg,pointerMapped⟩ := inv.typedReg pointer _ (inv.addr64 _ _ _ pointer source clif rfl)
  have noDefinition := stock_lower_source_parameter_definition run dominated events pointerBlock parameter
  have typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits) := by
    intro plain
    rw [valueType,width plain]
  have bodyRecords : body.records = [record] := by
    have scanned := split.scanned
    simp only [sourceBodyIndices,singleton,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.reverse_cons,
      List.reverse_nil,List.nil_append,Nat.add_zero] at scanned
    cases scanned with
    | cons head tail =>
      cases tail
      exact congrArg (fun r => [r]) (List.mem_singleton.mp member).symm
  exact ⟨⟨term,record,body,step,info,valueReg,pointerReg,split,bodyRecords,current,records,recorded,emitted,
    source,clif,typed,valueMapped,noDefinition,pointerMapped⟩⟩

end Backend.Stock.Memory.StoreRoots
