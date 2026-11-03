import FV.Backend.Proof.StockAcquireTwoLoadFinalFrontier

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual entry, both source reads, and both selected consumers construct the complete final frontier.
The proof recovers all demanded bindings internally before the real return record. -/
theorem two_load_returned_frontier {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {first second : BitVec 8}
    (read0 : cm.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : cm.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR [] cm world)
    (arguments : ArgsAtEntry F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world) :
    ∃ (records : TwoLoadRecords event) (block : VBlock) (prefixCode suffix : List MInst)
      (regs : Nat → CV) (nextWorld : Arm.ArmState),result.code.blocks[0]? = some block ∧
      block.insts.toList = prefixCode++records.terminal.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++suffix ∧
      seqRun isem prefixCode (entrySeed event.ctx (entry firstPointer secondPointer)) world = some (.fall regs nextWorld) ∧
      GuardedScanRel function result event.ctx event.block MR records.terminal.output.state
        (4,afterConsumer1 firstPointer secondPointer first second,cm) regs nextWorld := by
  obtain ⟨records⟩ := actual_two_load_records run scope dominated events schedule
  have member0 := records.member records.first (by simp)
  have member1 := records.member records.second (by simp)
  have member2 := records.member records.consumer0 (by simp)
  have member3 := records.member records.consumer1 (by simp)
  have blockAt : function.blocks[0]? = some function.blocks[0]! := by decide
  obtain ⟨source0,source1,source2,source3⟩ := actual_returned_source_relations run scope dominated events schedule env program firstPointer secondPointer cm first second read0 read1
  obtain ⟨entryEvent,block,prelude,after,regs0,world0,entryEvents,entryBlock,located,pieces,preludeRun,same,initial⟩ :=
    stock_lower_entry_pending_frontier run scope dominated (source_entry_pointers firstPointer secondPointer) driver memorySem stable memory arguments
  have eventEq := actual_single_event size entryEvents events
  subst entryEvent
  obtain ⟨history0,pending0,retiredMarks0,retiredValues0,related0⟩ := initial env program
  have indexed0 : IndexedSourceInst env program function event.ctx 0 records.first.inst
      (0,entry firstPointer secondPointer,cm) (1,afterFirst firstPointer secondPointer first,cm) :=
    ⟨by simp [records.pos0,blockStart],rfl,by simpa only [records.pos0] using source0⟩
  have prior0 : PendingGuardedScanRel function result event.ctx 0 env program MR
      (ReadEffectFrontier.empty event.ctx env program).history records.first.output.state
      (0,entry firstPointer secondPointer,cm) regs0 world0 := by
    rw [records.firstState]
    simpa only [entryBlock] using related0
  obtain ⟨frontier1,run0,related1,history1,retained1,pending1,retiredMarks1,retiredValues1⟩ :=
    stock_lower_sunk_frontier_step (isem := isem) run scope dominated events member0 records.marked0
      (bi := 0) (j := 0) (stm := ⟨[63],.atomicLoad .i8 {} 7⟩) blockAt (by decide) (by simp [records.pos0,blockStart]) indexed0 history0
      (by intro captured member;cases member)
      (by rw [records.firstState];exact pending0) (by rw [records.firstState];exact retiredMarks0)
      (by rw [records.firstState];exact retiredValues0) prior0
  have indexed1 : IndexedSourceInst env program function event.ctx 0 records.second.inst
      (1,afterFirst firstPointer secondPointer first,cm) (2,afterSecond firstPointer secondPointer first second,cm) :=
    ⟨by simp [records.pos1,blockStart],rfl,by simpa only [records.pos1] using source1⟩
  obtain ⟨frontier2,run1,related2,history2,retained2,pending2,retiredMarks2,retiredValues2⟩ :=
    stock_lower_sunk_frontier_step (isem := isem) run scope dominated events member1 records.marked1
      (bi := 0) (j := 1) (stm := ⟨[64],.atomicLoad .i8 {} 31⟩) blockAt (by decide) (by simp [records.pos1,blockStart]) indexed1 history1 retained1
      (by rw [records.secondState];exact pending1) (by rw [records.secondState];exact retiredMarks1)
      (by rw [records.secondState];exact retiredValues1) (by rw [records.secondState];exact related1)
  obtain ⟨R0,consume0⟩ := stock_lower_acquire_consumer_frontier_step run scope dominated events member2 records.recorded0 records.emitted0 records.selected0
  obtain ⟨pi0,ci0,producer0,value0,pointer0,ty0,flags0⟩ := first_consumer_endpoints entryBlock records.pos2 R0
  have body0 : (entry firstPointer secondPointer).body = R0.block.body := by
    have actualBlock := R0.blockAt
    rw [entryBlock] at actualBlock
    have equal := Option.some.inj (blockAt.symm.trans actualBlock)
    rw [← equal]
    rfl
  have actualHistory2 : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R0.consumerIndex)
      (entry firstPointer secondPointer,cm) (afterSecond firstPointer secondPointer first second,cm) frontier2.history := by
    simpa only [ci0,records.parts,List.take_succ_cons,List.take_zero,List.nil_append,List.cons_append,List.append_nil] using history2
  have actualRelated2 : PendingGuardedScanRel function result event.ctx event.block env program MR frontier2.history
      records.consumer0.output.state (R0.consumerIndex,afterSecond firstPointer secondPointer first second,cm) regs0 world0 := by
    rw [entryBlock,ci0,records.consumer0State]
    exact related2
  obtain ⟨frontier3,regs3,world3,run2,related3,history3,retained3,pending3,retiredMarks3,retiredValues3⟩ :=
    consume0 env program (entry firstPointer secondPointer,cm) (afterSecond firstPointer secondPointer first second,cm)
      (afterConsumer0 firstPointer secondPointer first second,cm) body0 (by simpa only [records.pos2] using source2)
      F sb syms isem MR stable memorySem memoryOk frontier2 regs0 world0 actualHistory2
      (by rw [records.consumer0State];exact pending2) (by rw [records.consumer0State];exact retiredMarks2)
      (by rw [records.consumer0State];exact retiredValues2) actualRelated2
  obtain ⟨R1,consume1⟩ := stock_lower_acquire_consumer_frontier_step run scope dominated events member3 records.recorded1 records.emitted1 records.selected1
  obtain ⟨pi1,ci1,producer1,value1,pointer1,ty1,flags1⟩ := second_consumer_endpoints entryBlock records.pos3 R1
  have body1 : (entry firstPointer secondPointer).body = R1.block.body := by
    have actualBlock := R1.blockAt
    rw [entryBlock] at actualBlock
    have equal := Option.some.inj (blockAt.symm.trans actualBlock)
    rw [← equal]
    rfl
  have actualHistory3 : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R1.consumerIndex)
      (entry firstPointer secondPointer,cm) (afterConsumer0 firstPointer secondPointer first second,cm) frontier3.history := by
    simpa only [ci0,ci1,records.parts,List.take_succ_cons,List.take_zero,List.nil_append,List.cons_append,List.append_nil] using history3
  have actualRelated3 : PendingGuardedScanRel function result event.ctx event.block env program MR frontier3.history
      records.consumer1.output.state (R1.consumerIndex,afterConsumer0 firstPointer secondPointer first second,cm) regs3 world3 := by
    rw [records.consumer1State,ci1]
    simpa only [ci0] using related3
  obtain ⟨frontier4,regs4,world4,run3,related4,history4,retained4,pending4,retiredMarks4,retiredValues4⟩ :=
    consume1 env program (entry firstPointer secondPointer,cm) (afterConsumer0 firstPointer secondPointer first second,cm)
      (afterConsumer1 firstPointer secondPointer first second,cm) body1 (by simpa only [records.pos3] using source3)
      F sb syms isem MR stable memorySem memoryOk frontier3 regs3 world3 actualHistory3
      (by rw [records.consumer1State];exact pending3) (by rw [records.consumer1State];exact retiredMarks3)
      (by rw [records.consumer1State];exact retiredValues3) actualRelated3
  have actualHistory4 : SourceReadCaptures event.ctx env program (event.output.records.reverse.take 4)
      (entry firstPointer secondPointer,cm) (afterConsumer1 firstPointer secondPointer first second,cm) frontier4.history := by
    simpa only [ci1,records.parts,List.take_succ_cons,List.take_zero,List.nil_append,List.cons_append,List.append_nil] using history4
  have finalRelated : PendingGuardedScanRel function result event.ctx event.block env program MR frontier4.history
      records.terminal.output.state (4,afterConsumer1 firstPointer secondPointer first second,cm) regs4 world4 := by
    rw [records.terminalState]
    simpa only [ci1] using related4
  have recovered := two_load_completed_guarded_recovery run scope events entryBlock records actualHistory4
    (by rw [records.terminalState];exact pending4) (by rw [records.terminalState];exact retiredValues4) finalRelated
  have emptyChunk : ∀ record ∈ event.output.records,record.input.sunk[record.inst]! = true → record.output.emitted = #[] := by
    intro record member marked
    have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record member
    exact congrArg Scan.emitted (Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked)))
  have empty0 := emptyChunk records.first member0 records.marked0
  have empty1 := emptyChunk records.second member1 records.marked1
  obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run events
  have eventCode : event.output.code = records.consumer0.output.emitted++records.consumer1.output.emitted++records.terminal.output.emitted := by
    apply Array.toList_inj.mp
    simp only [assembly,records.parts,List.flatMap_cons,List.flatMap_nil,empty0,empty1,Array.toList_empty,
      List.nil_append,List.append_nil,Array.toList_append,List.append_assoc]
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨records,block,prelude.toList++records.consumer0.output.emitted.toList.map (·.mapRegs resolve)++
    records.consumer1.output.emitted.toList.map (·.mapRegs resolve),after.toList,regs4,world4,located,?_,?_,recovered⟩
  · simp only [pieces,eventCode,Array.map_append,Array.toList_append,Array.toList_map,List.append_assoc,resolve]
  · exact seqRun_append_fall' isem (seqRun_append_fall' isem preludeRun run2) run3

end Backend.Stock.Proof.AcquireTwoLoadPrefix
