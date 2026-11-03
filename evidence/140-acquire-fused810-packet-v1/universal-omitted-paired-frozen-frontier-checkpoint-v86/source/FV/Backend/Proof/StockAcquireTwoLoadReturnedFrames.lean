import FV.Backend.Proof.StockAcquireTwoLoadActualSource
import FV.Backend.Proof.StockAcquireConsumerSourceUpdate

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

def afterSecond (firstPointer secondPointer : BitVec 64) (first second : BitVec 8) : Clif.Frame := {
  afterFirst firstPointer secondPointer first with
  regs := (afterFirst firstPointer secondPointer first).regs.set 64 ⟨.i8,second⟩
  body := function.blocks[0]!.body.drop 2 }

def afterConsumer0 (firstPointer secondPointer : BitVec 64) (first second : BitVec 8) : Clif.Frame := {
  afterSecond firstPointer secondPointer first second with
  regs := (afterSecond firstPointer secondPointer first second).regs.set 100 ⟨.i64,first.setWidth 64⟩
  body := function.blocks[0]!.body.drop 3 }

def afterConsumer1 (firstPointer secondPointer : BitVec 64) (first second : BitVec 8) : Clif.Frame := {
  afterConsumer0 firstPointer secondPointer first second with
  regs := (afterConsumer0 firstPointer secondPointer first second).regs.set 101 ⟨.i64,second.setWidth 64⟩
  body := function.blocks[0]!.body.drop 4 }

/-- The actual second producer's metadata derives its successful source relation with the original value. -/
theorem actual_second_source_result {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (entryBlock : event.block = 0) (position : record.inst = 3)
    (R : SourceEndpointReceipt function event record)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (first second : BitVec 8)
    (loaded : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second) :
    SourceInstResult env program event.ctx 1 (afterFirst firstPointer secondPointer first,memory)
      (afterSecond firstPointer secondPointer first second,memory) := by
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := second_consumer_endpoints entryBlock position R
  have results := mapped_atomic_result_singleton (stock_lower_record_context run scope events).1 R.defined R.installed R.source
  rw [value] at results
  have installed : event.ctx.insts[1]? = some R.info := by rw [← producer];exact R.installed
  have original : R.info.clif = some (.atomicLoad .i8 {} 31) := by rw [← ty,← flags,← pointer];exact R.source
  refine ⟨R.info,.atomicLoad .i8 {} 31,[⟨.i8,second⟩],(afterSecond firstPointer secondPointer first second).regs,
    function.blocks[0]!.body.drop 2,installed,original,?_,?_,?_,rfl⟩
  · rw [results]
    rfl
  · simp [instOutcome,Clif.evalInst,afterFirst,entry,Clif.Regs.set,Clif.Frame.get,Clif.Res.ofOption,Clif.Res.check,
      bind,Clif.Res.bind,Nat.mod_one,Clif.Ty.width,Clif.Ty.bytes,loaded]
  · rw [results]
    rfl

/-- Actual consumer 0 derives the exact original widening result and its source register update. -/
theorem actual_consumer0_source_result {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (entryBlock : event.block = 0) (position : record.inst = 2)
    (R : SourceEndpointReceipt function event record)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (first second : BitVec 8) :
    SourceInstResult env program event.ctx 2 (afterSecond firstPointer secondPointer first second,memory)
      (afterConsumer0 firstPointer secondPointer first second,memory) := by
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := first_consumer_endpoints entryBlock position R
  have blockAt := R.blockAt
  rw [entryBlock] at blockAt
  have originalAt : function.blocks[0]? = some function.blocks[0]! := by decide
  have blockEq := Option.some.inj (originalAt.symm.trans blockAt)
  have consumerAt := R.consumerAt
  rw [← blockEq,consumerIndex] at consumerAt
  have consumerStmt : R.consumerStmt = ⟨[100],.extend .uextend .i64 63⟩ := by simpa [function] using consumerAt.symm
  have extension := R.extension
  rw [consumerStmt] at extension
  have target : R.target = .i64 := (Clif.Inst.extend.inj extension.symm).2.1
  have results := source_endpoint_consumer_results run scope events R
  rw [consumerStmt] at results
  have installed : event.ctx.insts[2]? = some R.rootInfo := by rw [← position];exact R.rootInstalled
  have original : R.rootInfo.clif = some (.extend .uextend .i64 63) := by rw [← target,← value];exact R.rootSource
  refine ⟨R.rootInfo,.extend .uextend .i64 63,[⟨.i64,first.setWidth 64⟩],(afterConsumer0 firstPointer secondPointer first second).regs,
    function.blocks[0]!.body.drop 3,installed,original,?_,?_,?_,rfl⟩
  · rw [results]
    rfl
  · simp [instOutcome,Clif.evalInst,afterConsumer0,afterSecond,afterFirst,entry,Clif.Regs.set,Clif.Frame.get,
      Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Clif.Sem.uextend,Clif.Ty.width]
  · rw [results]
    rfl

/-- Actual consumer 1 derives the exact original widening result and its source register update. -/
theorem actual_consumer1_source_result {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (entryBlock : event.block = 0) (position : record.inst = 3)
    (R : SourceEndpointReceipt function event record)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (first second : BitVec 8) :
    SourceInstResult env program event.ctx 3 (afterConsumer0 firstPointer secondPointer first second,memory)
      (afterConsumer1 firstPointer secondPointer first second,memory) := by
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := second_consumer_endpoints entryBlock position R
  have blockAt := R.blockAt
  rw [entryBlock] at blockAt
  have originalAt : function.blocks[0]? = some function.blocks[0]! := by decide
  have blockEq := Option.some.inj (originalAt.symm.trans blockAt)
  have consumerAt := R.consumerAt
  rw [← blockEq,consumerIndex] at consumerAt
  have consumerStmt : R.consumerStmt = ⟨[101],.extend .uextend .i64 64⟩ := by simpa [function] using consumerAt.symm
  have extension := R.extension
  rw [consumerStmt] at extension
  have target : R.target = .i64 := (Clif.Inst.extend.inj extension.symm).2.1
  have results := source_endpoint_consumer_results run scope events R
  rw [consumerStmt] at results
  have installed : event.ctx.insts[3]? = some R.rootInfo := by rw [← position];exact R.rootInstalled
  have original : R.rootInfo.clif = some (.extend .uextend .i64 64) := by rw [← target,← value];exact R.rootSource
  refine ⟨R.rootInfo,.extend .uextend .i64 64,[⟨.i64,second.setWidth 64⟩],(afterConsumer1 firstPointer secondPointer first second).regs,
    function.blocks[0]!.body.drop 4,installed,original,?_,?_,?_,rfl⟩
  · rw [results]
    rfl
  · simp [instOutcome,Clif.evalInst,afterConsumer0,afterSecond,afterFirst,entry,Clif.Regs.set,Clif.Frame.get,
      Clif.Res.ofOption,Clif.Res.check,bind,Clif.Res.bind,Clif.Sem.uextend,Clif.Ty.width]
  · rw [results]
    rfl

end Backend.Stock.Proof.AcquireTwoLoadPrefix
