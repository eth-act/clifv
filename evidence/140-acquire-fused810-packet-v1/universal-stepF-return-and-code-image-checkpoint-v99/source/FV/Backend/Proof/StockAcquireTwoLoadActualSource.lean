import FV.Backend.Proof.StockAcquireTwoLoadExecutionWitness
import FV.Backend.Proof.StockAcquireTwoLoadEndpoints

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The original first read updates only its original result before the second source instruction. -/
def afterFirst (firstPointer secondPointer : BitVec 64) (raw : BitVec 8) : Clif.Frame := {
  entry firstPointer secondPointer with
  regs := (entry firstPointer secondPointer).regs.set 63 ⟨.i8,raw⟩
  body := function.blocks[0]!.body.drop 1 }

/-- Actual context metadata connects the original successful first read to SourceInstResult. -/
theorem actual_first_source_result {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (entryBlock : event.block = 0) (position : record.inst = 2)
    (R : SourceEndpointReceipt function event record)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (raw : BitVec 8)
    (loaded : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok raw) :
    SourceInstResult env program event.ctx 0 (entry firstPointer secondPointer,memory)
      (afterFirst firstPointer secondPointer raw,memory) := by
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := first_consumer_endpoints entryBlock position R
  have results := mapped_atomic_result_singleton (stock_lower_record_context run scope events).1 R.defined R.installed R.source
  rw [value] at results
  have installed : event.ctx.insts[0]? = some R.info := by rw [← producer];exact R.installed
  have original : R.info.clif = some (.atomicLoad .i8 {} 7) := by rw [← ty,← flags,← pointer];exact R.source
  refine ⟨R.info,.atomicLoad .i8 {} 7,[⟨.i8,raw⟩],(afterFirst firstPointer secondPointer raw).regs,
    function.blocks[0]!.body.drop 1,installed,original,?_,?_,?_,rfl⟩
  · rw [results]
    rfl
  · simp [instOutcome,Clif.evalInst,entry,Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,
      Nat.mod_one,Clif.Ty.width,Clif.Ty.bytes,loaded]
  · rw [results]
    rfl

/-- Actual context metadata connects the second original read fault to SourceInstFault after first-read success. -/
theorem actual_second_source_fault {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (entryBlock : event.block = 0) (position : record.inst = 3)
    (R : SourceEndpointReceipt function event record)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (raw : BitVec 8) (code : Clif.TrapCode)
    (failed : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .trap code) :
    SourceInstFault env program event.ctx 1 (afterFirst firstPointer secondPointer raw,memory) code := by
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := second_consumer_endpoints entryBlock position R
  have results := mapped_atomic_result_singleton (stock_lower_record_context run scope events).1 R.defined R.installed R.source
  rw [value] at results
  have installed : event.ctx.insts[1]? = some R.info := by rw [← producer];exact R.installed
  have original : R.info.clif = some (.atomicLoad .i8 {} 31) := by rw [← ty,← flags,← pointer];exact R.source
  refine ⟨R.info,.atomicLoad .i8 {} 31,function.blocks[0]!.body.drop 2,installed,original,?_,?_⟩
  · rw [results]
    rfl
  · simp [instOutcome,Clif.evalInst,afterFirst,entry,Clif.Regs.set,Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,
      bind,Clif.Res.bind,Nat.mod_one,Clif.Ty.width,Clif.Ty.bytes,failed]

end Backend.Stock.Proof.AcquireTwoLoadPrefix
