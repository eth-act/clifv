import FV.Backend.Proof.StockMemoryRetainedStoreReturnSpec
import FV.Backend.Proof.StockStoreMixedRetention

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Store retention and operand mappings are internal consequences of original source syntax. -/
theorem stock_mixed_store_record_spec (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j value pointer : Nat} {flags : Clif.MemFlags}
    (statement : b.body[j]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩)
    {pi vi : Nat} {pb vb : Clif.Block} {valueTy : Clif.Ty}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
    Nonempty (RetainedStoreReturnSpec kind ty f result event b j value pointer flags) := by
  obtain ⟨term,record,body,step,split,member,current,unsunk,actual,records,recorded,emitted⟩ :=
    stock_lower_mixed_store_emitted run scope events block statement
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



end Backend.Stock.Memory.StoreRoots
