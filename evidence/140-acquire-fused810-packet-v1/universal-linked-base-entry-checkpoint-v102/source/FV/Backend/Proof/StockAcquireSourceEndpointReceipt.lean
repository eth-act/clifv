import FV.Backend.Proof.StockAcquireSourceLoadedPrefix

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Internal source facts derived from the actual retained selection; never a compiler admission input. -/
structure SourceEndpointReceipt (f : Clif.Function) (event : BlockScanEvent) (record : ScanRecord) where
  original : Ctx
  ranges : Array (Nat × Nat)
  initial : LState
  block : Clif.Block
  producerIndex : Nat
  consumerIndex : Nat
  value : Nat
  producer : Nat
  producerStmt : Clif.Stmt
  consumerStmt : Clif.Stmt
  info : IInfo
  rootInfo : IInfo
  ty : Clif.Ty
  target : Clif.Ty
  flags : Clif.MemFlags
  pointer : Nat
  built : Backend.buildCtx f = .ok (original,ranges,initial)
  blockAt : f.blocks[event.block]? = some block
  producerAt : block.body[producerIndex]? = some producerStmt
  consumerAt : block.body[consumerIndex]? = some consumerStmt
  position : producer = blockStart f event.block+producerIndex
  current : record.inst = blockStart f event.block+consumerIndex
  before : producerIndex < consumerIndex
  atomic : producerStmt.inst = .atomicLoad ty flags pointer
  extension : consumerStmt.inst = .extend .uextend target value
  result : value ∈ producerStmt.results
  defined : event.ctx.defInst? value = some producer
  installed : event.ctx.insts[producer]? = some info
  source : info.clif = some (.atomicLoad ty flags pointer)
  rootInstalled : event.ctx.insts[record.inst]? = some rootInfo
  rootSource : rootInfo.clif = some (.extend .uextend target value)
  integer : eTy ty = true
  little : flags.endianness ≠ some .big
  fits : target.width ≤ 64

/-- Actual selection and original admission construct the complete internal endpoint receipt. -/
theorem stock_lower_acquire_source_endpoint_receipt {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) : Nonempty (SourceEndpointReceipt f event record) := by
  obtain ⟨original,ranges,initial,block,producerIndex,consumerIndex,value,producer,producerStmt,consumerStmt,
    info,rootInfo,ty,target,flags,pointer,built,blockAt,producerAt,consumerAt,position,current,before,
    atomic,extension,valueResult,defined,installed,source,rootInstalled,rootSource,integer,little,fits⟩ :=
    stock_lower_acquire_selected_source_endpoints run scope dominated events records recorded emitted selectedId
  exact ⟨⟨original,ranges,initial,block,producerIndex,consumerIndex,value,producer,producerStmt,consumerStmt,
    info,rootInfo,ty,target,flags,pointer,built,blockAt,producerAt,consumerAt,position,current,before,
    atomic,extension,valueResult,defined,installed,source,rootInstalled,rootSource,integer,little,fits⟩⟩

end Backend.Stock.Proof.Acquire810
