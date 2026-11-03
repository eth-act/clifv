import FV.Backend.Proof.StockAcquireTwoLoadSchedule

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual ABI entry and the first successful source read construct the first captured frontier.
This internal composition keeps the complete fixed body and every later fault alternative. -/
theorem two_load_entry_first_capture {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame} (entered : SourceEntry function args frame)
    {env : Clif.Env} {program : Clif.Program} {after : Clif.Frame × Clif.Mem}
    (source : SourceInstResult env program event.ctx 0 (frame,cm) after)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F function.sig args world) :
    ∃ (first : ScanRecord) (block : VBlock) (prelude suffix : Array MInst)
      (regs : Nat → CV) (nextWorld : Arm.ArmState) (frontier : ReadEffectFrontier event.ctx env program),
      first ∈ event.output.records ∧ first.inst = 0 ∧ result.code.blocks[0]? = some block ∧
      block.insts = prelude++event.output.code.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++suffix ∧
      seqRun isem prelude.toList (entrySeed event.ctx frame) world = some (.fall regs nextWorld) ∧
      SameWorld F nextWorld world ∧
      seqRun isem (first.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs nextWorld =
          some (.fall regs nextWorld) ∧
      SourceReadCaptures event.ctx env program [first] (frame,cm) after frontier.history ∧
      (∀ captured ∈ frontier.history,captured.record ∈ event.output.records) ∧
      PendingReadMarks frontier first.input ∧ RetiredReadUnmarked frontier first.input ∧
      RetiredUndemanded frontier first.input ∧
      PendingGuardedScanRel function result event.ctx 0 env program MR frontier.history first.input (1,after) regs nextWorld := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,firstIndex,secondIndex,consumer0Index,consumer1Index,terminalIndex⟩ :=
    actual_schedule_records schedule
  obtain ⟨entryEvent,block,prelude,suffix,regs,nextWorld,entryEvents,entryBlock,located,pieces,executed,same,initial⟩ :=
    stock_lower_entry_pending_frontier run scope dominated entered driver memorySem stable memory arguments
  have eventEq := actual_single_event size entryEvents events
  subst entryEvent
  rcases schedule with ⟨eventBlock,indices,firstState,secondState,consumer0State,consumer1State,terminalState,
    firstMarked,secondMarked,firstRoot,secondRoot,firstEmitted,secondEmitted⟩
  have firstStateEq : first.output.state = event.output.state := by
    simpa only [parts,List.getElem!_cons_zero] using firstState
  have marked : first.input.sunk[first.inst]! = true := by
    simpa only [parts,List.getElem!_cons_zero,firstIndex] using firstMarked
  have retained : first ∈ event.output.records := by
    apply List.mem_reverse.mp
    rw [parts]
    exact List.mem_cons_self ..
  obtain ⟨history,pending,retiredMarks,retiredValues,related⟩ := initial env program
  have firstRelated : PendingGuardedScanRel function result event.ctx 0 env program MR
      (ReadEffectFrontier.empty event.ctx env program).history first.output.state (0,frame,cm) regs nextWorld := by
    rw [firstStateEq]
    simpa only [entryBlock] using related
  have firstPending : PendingReadMarks (ReadEffectFrontier.empty event.ctx env program) first.output.state := by
    rw [firstStateEq];exact pending
  have firstRetiredMarks : RetiredReadUnmarked (ReadEffectFrontier.empty event.ctx env program) first.output.state := by
    rw [firstStateEq];exact retiredMarks
  have firstRetiredValues : RetiredUndemanded (ReadEffectFrontier.empty event.ctx env program) first.output.state := by
    rw [firstStateEq];exact retiredValues
  have indexed : IndexedSourceInst env program function event.ctx 0 first.inst (0,frame,cm) (1,after) :=
    ⟨by simp [firstIndex,blockStart],rfl,by simpa only [firstIndex] using source⟩
  obtain ⟨frontier,emptyCode,post,captured,allRetained,pendingAfter,retiredMarksAfter,retiredValuesAfter⟩ :=
    stock_lower_sunk_frontier_step run scope dominated events retained marked
      (bi := 0) (j := 0) (block := function.blocks[0]!) (stm := ⟨[63],.atomicLoad .i8 {} 7⟩)
      (by decide) (by decide) (by simp [firstIndex,blockStart]) indexed history
      (by intro captured member;cases member) firstPending firstRetiredMarks firstRetiredValues firstRelated
  exact ⟨first,block,prelude,suffix,regs,nextWorld,frontier,retained,firstIndex,located,pieces,executed,same,
    emptyCode,by simpa using captured,allRetained,pendingAfter,retiredMarksAfter,retiredValuesAfter,post⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
