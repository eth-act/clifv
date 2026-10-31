import FV.Backend.Proof.StockMemoryStoreReturnSpec
import FV.Backend.Proof.StockMemoryRetainedReturnSpec

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual store data for composition comes from original syntax and the complete driver. -/
structure RetainedStoreReturnSpec (kind : Kind) (ty : Clif.Ty) (f : Clif.Function) (result : Result)
    (event : BlockScanEvent) (b : Clif.Block) (j value pointer : Nat) (flags : Clif.MemFlags) where
  term : ScanRecord
  record : ScanRecord
  body : BlockScan
  step : Step
  info : IInfo
  valueReg : Nat
  pointerReg : Nat
  split : SourceBodySplit f event b term body
  bodyMember : record ∈ body.records
  current : record.inst = blockStart f event.block+j
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
theorem stock_retained_store_return_spec (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j value pointer : Nat} {flags : Clif.MemFlags}
    (statement : b.body[j]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩) (ret : b.term = .ret [])
    {pi vi : Nat} {pb vb : Clif.Block} {valueTy : Clif.Ty}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
    Nonempty (RetainedStoreReturnSpec kind ty f result event b j value pointer flags) := by
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
  exact ⟨⟨term,record,body,step,info,valueReg,pointerReg,split,member,current,records,recorded,emitted,
    source,clif,typed,valueMapped,noDefinition,pointerMapped⟩⟩


/-- Classify every actual body record from the original store/NOP syntax.
The selected record identity follows from unique original scan positions. -/
theorem RetainedStoreReturnSpec.nop_records
    {kind : Kind} {ty : Clif.Ty} {f : Clif.Function} {result : Result} {event : BlockScanEvent}
    {b : Clif.Block} {storeIndex value pointer : Nat} {flags : Clif.MemFlags}
    (spec : RetainedStoreReturnSpec kind ty f result event b storeIndex value pointer flags)
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (events : event ∈ result.blockScans.toList)
    (shape : ∀ j stm,b.body[j]? = some stm → j = storeIndex ∨ stm.inst = .nop) :
    ∀ record ∈ spec.body.records,record = spec.record ∨
      ∃ step,record.output.step = some step ∧ step.decision = .omitted := by
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  intro record member
  obtain ⟨j,stm,statement,current⟩ := spec.split.positions record member
  rcases shape j stm statement with selected | nop
  · left
    subst j
    exact spec.split.scanned.record_unique unique member spec.bodyMember
      (current.trans spec.current.symm)
  · right
    exact MaskBody.actual_nop_record_at_block run scope events spec.split member statement current nop


end Backend.Stock.Memory.StoreRoots
