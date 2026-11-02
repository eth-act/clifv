import FV.Backend.Proof.StockMemoryStoreDemandTransport
import FV.Backend.Proof.StockMemoryIntegerRetainedReturnSpec

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Stored load results derive complete retained-load data without a return use.
The store RHS supplies the demand and sink guard for the actual source definition. -/
theorem stock_retained_integer_stored_load_spec (width : IntegerRoots.Width) (kind : Kind) (ty : Clif.Ty)
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {j value pointer : Nat} {storeFlags : Clif.MemFlags}
    (store : RetainedStoreReturnSpec kind ty f result event b j value pointer storeFlags)
    {i x : Nat} {flags : Clif.MemFlags}
    (statement : b.body[i]? = some ⟨[value],.load .load width.sourceTy flags x 0⟩)
    (earlier : i < j)
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (parameter : x ∈ pb.params.map (·.1)) :
    Nonempty (IntegerRoots.RetainedIntegerLoadReturnSpec width f result event b i x value flags) := by
  obtain ⟨record,step,member,current,unsunk,demanded,actual,records,recorded,emitted⟩ :=
    stock_retained_stored_definition_emitted kind ty run scope dominated events store statement earlier (by simp)
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events store.split statement current
  obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan actual recorded emitted
  have atInst : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun (by rw [atInst,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg value r mapped
  obtain ⟨nreg,pointer⟩ := inv.typedReg x _ (inv.addr64 _ _ _ x source clif rfl)
  have noDefinition := stock_lower_source_parameter_definition run dominated events parameterBlock parameter
  exact ⟨⟨store.term,record,store.body,step,info,a,nreg,store.split,member,current,records,recorded,
    emitted,source,clif,results,mapped,noDefinition,pointer⟩⟩

end Backend.Stock.Memory.StoreRoots
