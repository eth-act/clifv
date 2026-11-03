import FV.Backend.Proof.StockAcquireTwoLoadRecords
import FV.Backend.Proof.StockAcquireTwoLoadOriginalReturned

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual retained metadata derives every successful source relation through both consumers. -/
theorem actual_returned_source_relations {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (first second : BitVec 8)
    (read0 : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second) :
    SourceInstResult env program event.ctx 0 (entry firstPointer secondPointer,memory)
      (afterFirst firstPointer secondPointer first,memory) ∧
    SourceInstResult env program event.ctx 1 (afterFirst firstPointer secondPointer first,memory)
      (afterSecond firstPointer secondPointer first second,memory) ∧
    SourceInstResult env program event.ctx 2 (afterSecond firstPointer secondPointer first second,memory)
      (afterConsumer0 firstPointer secondPointer first second,memory) ∧
    SourceInstResult env program event.ctx 3 (afterConsumer0 firstPointer secondPointer first second,memory)
      (afterConsumer1 firstPointer secondPointer first second,memory) := by
  obtain ⟨records⟩ := actual_two_load_records run scope dominated events schedule
  exact ⟨actual_first_source_result run scope events schedule.1 records.pos2 records.R0 env program firstPointer secondPointer memory first read0,
    actual_second_source_result run scope events schedule.1 records.pos3 records.R1 env program firstPointer secondPointer memory first second read1,
    actual_consumer0_source_result run scope events schedule.1 records.pos2 records.R0 env program firstPointer secondPointer memory first second,
    actual_consumer1_source_result run scope events schedule.1 records.pos3 records.R1 env program firstPointer secondPointer memory first second⟩

/-- Both successful original reads compose with both actual widening steps in source order. -/
theorem actual_returned_source_steps {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (first second : BitVec 8)
    (read0 : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second) :
    SourceSteps (SourceInstResult env program event.ctx) [0,1,2,3]
      (entry firstPointer secondPointer,memory) (afterConsumer1 firstPointer secondPointer first second,memory) := by
  obtain ⟨step0,step1,step2,step3⟩ := actual_returned_source_relations run scope dominated events schedule env program firstPointer secondPointer memory first second read0 read1
  exact .cons step0 (.cons step1 (.cons step2 (.cons step3 (.nil _))))

/-- Original public returned execution supplies the complete indexed source prefix internally. -/
theorem original_returned_source_steps {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {args : List Clif.Val} {state : Clif.State} (entered : ClifEntry function args state)
    (env : Clif.Env) (program : Clif.Program) (fuel : Nat) {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel state = .returned values final) :
    ∃ after,SourceSteps (SourceInstResult env program event.ctx) [0,1,2,3] (state.frame,state.mem) after ∧
      after.2 = state.mem ∧ after.1.body = [] ∧ final = (state.mem.free []).leave := by
  obtain ⟨firstPointer,secondPointer,first,second,arguments,frame,callers,read0,read1,valuesEq,memoryEq⟩ := original_returned_reads entered env program fuel returned
  refine ⟨(afterConsumer1 firstPointer secondPointer first second,state.mem),?_,rfl,rfl,memoryEq⟩
  rw [frame]
  exact actual_returned_source_steps run scope dominated events schedule env program firstPointer secondPointer state.mem first second read0 read1

end Backend.Stock.Proof.AcquireTwoLoadPrefix
