import FV.Backend.Proof.StockMemoryIntegerReturnSpec
import FV.Backend.Proof.StockMaskBlockRecords
import FV.Backend.Proof.StockScanTrapSemantics

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structure RetainedIntegerLoadReturnSpec (width : Width) (f : Clif.Function) (result : Result) (event : BlockScanEvent)
    (b : Clif.Block) (j x z : Nat) (flags : Clif.MemFlags) where
  term : ScanRecord
  record : ScanRecord
  body : BlockScan
  step : Step
  info : IInfo
  resultReg : Nat
  pointerReg : Nat
  split : SourceBodySplit f event b term body
  bodyMember : record ∈ body.records
  current : record.inst = blockStart f event.block+j
  records : record ∈ event.output.records
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.load .load width.sourceTy flags x 0)
  results : info.results = [z]
  mapped : event.ctx.valueReg? z = some (.vreg resultReg .int)
  parameter : event.ctx.defInst? x = none
  pointer : event.ctx.valueReg? x = some (.vreg pointerReg .int)


/-- Derive the retained load at its original source position, including inherited parameter pointers. -/
theorem stock_retained_integer_load_return_spec (width : Width) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j x z : Nat} {flags : Clif.MemFlags}
    (statement : b.body[j]? = some ⟨[z],.load .load width.sourceTy flags x 0⟩) (ret : b.term = .ret [z])
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (parameter : x ∈ pb.params.map (·.1))
    : Nonempty (RetainedIntegerLoadReturnSpec width f result event b j x z flags) := by
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
  exact ⟨⟨term,record,body,step,info,a,nreg,split,member,current,records,recorded,emitted,
    source,clif,results,mapped,noDefinition,pointer⟩⟩

end Backend.Stock.Memory.IntegerRoots
