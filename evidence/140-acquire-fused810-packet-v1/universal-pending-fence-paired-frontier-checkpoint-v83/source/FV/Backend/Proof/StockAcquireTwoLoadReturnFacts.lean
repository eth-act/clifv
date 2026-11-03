import FV.Backend.Proof.StockAcquireTwoLoadReturnedSourceSteps
import FV.Backend.Proof.StockSourceEntry
import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Original source entry and all actual source steps derive final definedness internally. -/
theorem actual_returned_source_defined {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (first second : BitVec 8)
    (read0 : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second) :
    SourceDefinedAt function result.ctx event.block 4 (afterConsumer1 firstPointer secondPointer first second) := by
  obtain ⟨step0,step1,step2,step3⟩ := actual_returned_source_relations run scope dominated events schedule env program firstPointer secondPointer memory first second read0 read1
  have blockAt : function.blocks[0]? = some function.blocks[0]! := by decide
  have initial := source_defined_entry_frame dominated result.ctx (source_entry_pointers firstPointer secondPointer)
  have defined0 := stock_lower_source_defined_step run scope dominated events (bi := 0) (j := 0)
    (stm := ⟨[63],.atomicLoad .i8 {} 7⟩) blockAt (by decide) rfl initial step0
  have defined1 := stock_lower_source_defined_step run scope dominated events (bi := 0) (j := 1)
    (stm := ⟨[64],.atomicLoad .i8 {} 31⟩) blockAt (by decide) rfl defined0 step1
  have defined2 := stock_lower_source_defined_step run scope dominated events (bi := 0) (j := 2)
    (stm := ⟨[100],.extend .uextend .i64 63⟩) blockAt (by decide) rfl defined1 step2
  have defined3 := stock_lower_source_defined_step run scope dominated events (bi := 0) (j := 3)
    (stm := ⟨[101],.extend .uextend .i64 64⟩) blockAt (by decide) rfl defined2 step3
  simpa only [schedule.1] using defined3

/-- Actual source construction identifies the real final return index. -/
theorem actual_terminal_index {result : Result} (run : Stock.lower function = .ok result)
    (scope : LowerScope function) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    (entryBlock : event.block = 0) (records : TwoLoadRecords event) : records.terminal.inst = event.termInst := by
  obtain ⟨block,terminal,body,split⟩ := stock_lower_body_scan_split run scope events
  have originalAt : function.blocks[0]? = some function.blocks[0]! := by decide
  have actualAt := split.block
  rw [entryBlock] at actualAt
  have blockEq := Option.some.inj (originalAt.symm.trans actualAt)
  have termIndex := split.termIndex
  rw [← blockEq] at termIndex
  have finalIndex : event.termInst = 4 := by simpa [entryBlock,blockStart,function] using termIndex
  exact records.pos4.trans finalIndex.symm

/-- The exact source return frees and leaves the original source memory after both final bindings. -/
theorem source_return_term_done (env : Clif.Env) (program : Clif.Program)
    (firstPointer secondPointer : BitVec 64) (memory : Clif.Mem) (first second : BitVec 8) :
    Clif.stepTerm env program ⟨afterConsumer1 firstPointer secondPointer first second,[],memory⟩ (.ret [100,101]) =
      .done [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] (memory.free []).leave := by
  simp [Clif.stepTerm,Clif.returnValues,Clif.Frame.getMany,Clif.Frame.get,Clif.Regs.set,Clif.Res.ofOption,
    Clif.Res.check,bind,Clif.Res.bind,afterConsumer1,afterConsumer0,afterSecond,afterFirst,entry,function,
    Clif.Ty.width,Clif.checkTys,Clif.AbiParam.tys]

end Backend.Stock.Proof.AcquireTwoLoadPrefix
