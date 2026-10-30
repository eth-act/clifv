import FV.Backend.Proof.StockMemoryDispatch
import FV.Backend.Proof.StockReturnedSourceRetention

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original source parameters have no DFG instruction in each actual scan context. -/
theorem stock_lower_source_parameter_definition {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) {x : Nat}
    (parameter : x ∈ b.params.map (·.1)) : event.ctx.defInst? x = none := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,nodeBi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have defs : event.ctx.valDef = original.valDef := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valDef
  simpa only [Ctx.defInst?,defs] using defInst_par spec.facts dominated.ssa block parameter

/-- Proof-internal retained load-body data, derived from original source syntax.
Consumers receive this from the whole driver; it is never an accepted-input certificate. -/
structure SingleLoadReturnSpec (f : Clif.Function) (result : Result) (event : BlockScanEvent)
    (b : Clif.Block) (x z : Nat) (flags : Clif.MemFlags) where
  term : ScanRecord
  record : ScanRecord
  body : BlockScan
  step : Step
  info : IInfo
  resultReg : Nat
  pointerReg : Nat
  split : SourceBodySplit f event b term body
  bodyRecords : body.records = [record]
  current : record.inst = blockStart f event.block+0
  records : record ∈ event.output.records
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.load .load .i32 flags x 0)
  results : info.results = [z]
  mapped : event.ctx.valueReg? z = some (.vreg resultReg .int)
  parameter : event.ctx.defInst? x = none
  pointer : event.ctx.valueReg? x = some (.vreg pointerReg .int)

/-- Original singleton load/return syntax derives all retained-body data. -/
theorem stock_single_load_return_spec {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {x z : Nat} {flags : Clif.MemFlags}
    (singleton : b.body = [⟨[z],.load .load .i32 flags x 0⟩]) (ret : b.term = .ret [z])
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (parameter : x ∈ pb.params.map (·.1))
    : Nonempty (SingleLoadReturnSpec f result event b x z flags) := by
  have statement : b.body[0]? = some ⟨[z],.load .load .i32 flags x 0⟩ := by simp [singleton]
  obtain ⟨term,record,body,step,split,member,current,unsunk,actual,records,recorded,emitted⟩ :=
    stock_lower_returned_definition_emitted run scope dominated events block statement (z := z)
      (by simp) ret (by simp)
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan actual recorded emitted
  have atInst : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source,Option.getD_some]
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun (by rw [atInst,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  obtain ⟨nreg,pointer⟩ := inv.typedReg x _ (inv.addr64 _ _ _ x source clif rfl)
  have noDefinition := stock_lower_source_parameter_definition run dominated events parameterBlock parameter
  have bodyRecords : body.records = [record] := by
    have scanned := split.scanned
    simp only [sourceBodyIndices,singleton,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.reverse_cons,
      List.reverse_nil,List.nil_append,Nat.add_zero] at scanned
    cases scanned with
    | cons head tail =>
      cases tail
      exact congrArg (fun r => [r]) (List.mem_singleton.mp member).symm
  exact ⟨⟨term,record,body,step,info,a,nreg,split,bodyRecords,current,records,recorded,emitted,
    source,clif,results,mapped,noDefinition,pointer⟩⟩

end Backend.Stock.Memory
