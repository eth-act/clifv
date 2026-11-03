import FV.Backend.Proof.StockAcquireTwoLoadActualSource

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The first original fault derives its indexed relation without evaluating the second source load. -/
theorem actual_first_source_fault {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (entryBlock : event.block = 0) (position : record.inst = 2)
    (R : SourceEndpointReceipt function event record)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (code : Clif.TrapCode)
    (failed : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .trap code) :
    SourceInstFault env program event.ctx 0 (entry firstPointer secondPointer,memory) code := by
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := first_consumer_endpoints entryBlock position R
  have results := mapped_atomic_result_singleton (stock_lower_record_context run scope events).1 R.defined R.installed R.source
  rw [value] at results
  have installed : event.ctx.insts[0]? = some R.info := by rw [← producer];exact R.installed
  have original : R.info.clif = some (.atomicLoad .i8 {} 7) := by rw [← ty,← flags,← pointer];exact R.source
  refine ⟨R.info,.atomicLoad .i8 {} 7,function.blocks[0]!.body.drop 1,installed,original,?_,?_⟩
  · rw [results]
    rfl
  · simp [instOutcome,Clif.evalInst,entry,Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,
      bind,Clif.Res.bind,Nat.mod_one,Clif.Ty.width,Clif.Ty.bytes,failed]

end Backend.Stock.Proof.AcquireTwoLoadPrefix
