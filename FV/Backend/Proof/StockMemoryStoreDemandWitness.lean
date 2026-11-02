import FV.Backend.Proof.StockMemoryStoredLoadSpec
import FV.Backend.Proof.StockMemoryComputedStoreRecordWitness

namespace Backend.Stock.Memory.StoreRoots.ComputedFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def flags : Clif.MemFlags := {trapCode := none}
private theorem scope : LowerScope function := lowerScope_of (by native_decide)
private theorem dominated : Dominated function := dominated_of (by native_decide)

/-- The original captured copy function demands its first load through its store.
The function returns no loaded value. The witness uses actual retained records. -/
theorem captured_store_demand_before_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (spec : RetainedStoreReturnSpec .plain64 .i64 function result event b 3 2 0 flags)
      (record : ScanRecord),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧
      function.blocks[event.block]? = some b ∧
      b.body[1]? = some ⟨[2],.load .load .i64 flags 1 0⟩ ∧
      record ∈ spec.body.records ∧ record.inst = blockStart function event.block+1 ∧
      spec.record.inst = blockStart function event.block+3 ∧
      Demanded record.input 2 ∧ Demanded record.output.state 2 ∧
      DemandedUnsunkLe event.ctx spec.record.output.state record.input ∧
      DemandedUnsunkLe event.ctx spec.record.output.state record.output.state := by
  obtain ⟨f,result,event,b,same,name,sret,run,events,block,loadStatement,storeStatement,
    computed,valueType,spec⟩ := captured_computed_store_record_witness
  subst f
  obtain ⟨spec⟩ := spec
  have inside := (List.getElem?_eq_some_iff.mp loadStatement).1
  have indexed : blockStart function event.block+1 ∈ sourceBodyIndices function event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨1,List.mem_range.mpr inside,rfl⟩
  rw [← spec.split.scanned.order] at indexed
  obtain ⟨record,member,current⟩ := List.mem_map.mp indexed
  have earlier : record.inst < spec.record.inst := by rw [current,spec.current]; omega
  obtain ⟨_,pre,post,preFrame,postFrame⟩ := stock_retained_store_demand_before .plain64 .i64
    run scope dominated events spec member earlier
  exact ⟨result,event,b,spec,record,run,events,block,loadStatement,member,current,spec.current,
    pre,post,preFrame,postFrame⟩

/-- The unchanged captured function emits its first load although it returns nothing.
Its successful store supplies the sink guard and demand for that load. -/
theorem captured_stored_load_emitted_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block)
      (spec : RetainedStoreReturnSpec .plain64 .i64 function result event b 3 2 0 flags)
      (record : ScanRecord) (step : Step),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧
      function.blocks[event.block]? = some b ∧
      b.body[1]? = some ⟨[2],.load .load .i64 flags 1 0⟩ ∧
      record ∈ spec.body.records ∧ record.inst = blockStart function event.block+1 ∧
      record.input.sunk[record.inst]! = false ∧ Demanded record.input 2 ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input =
        .ok record.output ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨result,event,b,spec,old,run,events,block,statement,_⟩ := captured_store_demand_before_witness
  obtain ⟨record,step,member,current,safe,demanded,actual,records,recorded,emitted⟩ :=
    stock_retained_stored_definition_emitted .plain64 .i64 run scope dominated events spec
      statement (by decide +kernel) (by simp)
  exact ⟨result,event,b,spec,record,step,run,events,block,statement,member,current,safe,demanded,
    actual,records,recorded,emitted⟩

/-- The captured function inhabits complete load-record data through its store.
Its original source and inherited parameter address remain unchanged. -/
theorem captured_stored_load_spec_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block),
      Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧
      function.blocks[event.block]? = some b ∧
      b.body[1]? = some ⟨[2],.load .load .i64 flags 1 0⟩ ∧
      Nonempty (RetainedStoreReturnSpec .plain64 .i64 function result event b 3 2 0 flags) ∧
      Nonempty (IntegerRoots.RetainedIntegerLoadReturnSpec .w64 function result event b 1 1 2 flags) := by
  obtain ⟨result,event,b,store,record,run,events,block,statement,_⟩ := captured_store_demand_before_witness
  have entry : function.blocks[0]? = some function.blocks[0]! := by native_decide
  have parameter : 1 ∈ function.blocks[0]!.params.map (·.1) := by native_decide
  have load := stock_retained_integer_stored_load_spec .w64 .plain64 .i64 run scope dominated events
    store statement (by decide +kernel) entry parameter
  exact ⟨result,event,b,run,events,block,statement,⟨store⟩,load⟩

end Backend.Stock.Memory.StoreRoots.ComputedFixture
