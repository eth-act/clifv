import FV.Backend.Proof.StockAcquireTwoLoadReturnedFrontier
import FV.Backend.Proof.StockAcquireConsumerPairedFrontier
import FV.Backend.Proof.StockAcquirePairedEntryFrontier
import FV.Backend.Proof.StockAcquireSunkPairedFrontier

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Actual ABI entry and source reads construct both complete pending histories and recover every final binding. -/
theorem two_load_returned_paired_frontier {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {first second : BitVec 8}
    (read0 : cm.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : cm.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {world otherWorld : Arm.ArmState} (memory : MRP Γ function c D [] cm (world,otherWorld))
    (arguments : ArgsAtEntry Γ.F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world)
    (otherArguments : ArgsAtEntry Γ.F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] otherWorld)
    (registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈ (locsOf function.sig).zip [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] →
      regVal otherWorld pin = regVal world pin) :
    ∃ (records : TwoLoadRecords event) (block : VBlock) (prefixCode suffix : List MInst)
      (regs : Nat → CV) (nextWorld nextOther : Arm.ArmState),result.code.blocks[0]? = some block ∧
      block.insts.toList = prefixCode++records.terminal.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++suffix ∧
      seqRun (pairSem (valueSem Γ.F fc X)) prefixCode (entrySeed event.ctx (entry firstPointer secondPointer)) (world,otherWorld) =
        some (.fall regs (nextWorld,nextOther)) ∧
      GuardedScanRel function result event.ctx event.block (RelW Γ function c) records.terminal.output.state
        (4,afterConsumer1 firstPointer secondPointer first second,cm) regs nextWorld ∧
      GuardedScanRel function result event.ctx event.block (RelW Γ function c) records.terminal.output.state
        (4,afterConsumer1 firstPointer secondPointer first second,cm) regs nextOther ∧
      SameWorld (Zof Γ.F D cm) nextWorld nextOther := by
  let isem := valueSem Γ.F fc X
  let MR := RelW Γ function c
  let F := Γ.F
  let sb := Γ.slotOff
  let syms := Γ.syms
  have stable := mrStable_relW Γ function c
  have memorySem := memRefines_valueSem Γ.F fc X slot symbols
  have memoryOk := memRelOk_relW Γ function c
  let world0 := world
  let other0 := otherWorld
  obtain ⟨records⟩ := actual_two_load_records run scope dominated events schedule
  have member0 := records.member records.first (by simp)
  have member1 := records.member records.second (by simp)
  have member2 := records.member records.consumer0 (by simp)
  have member3 := records.member records.consumer1 (by simp)
  have blockAt : function.blocks[0]? = some function.blocks[0]! := by decide
  obtain ⟨source0,source1,source2,source3⟩ := actual_returned_source_relations run scope dominated events schedule env program firstPointer secondPointer cm first second read0 read1
  have registerOnly : ∀ loc ∈ locsOf function.sig,∃ pin,loc = .reg pin := by
    intro loc member
    change loc ∈ [.reg (.x 0),.reg (.x 1)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨_,rfl⟩
  obtain ⟨entryEvent,block,prelude,after,regs0,entryEvents,entryBlock,located,pieces,preludeRun,initial⟩ :=
    E2E.StockAcquirePair.stock_lower_entry_paired_pending_frontier run scope dominated
      (source_entry_pointers firstPointer secondPointer) registerOnly slot symbols memory arguments otherArguments registers
  have eventEq := actual_single_event size entryEvents events
  subst entryEvent
  obtain ⟨history0,pending0,retiredMarks0,retiredValues0,related0,otherRelated0⟩ := initial env program
  have indexed0 : IndexedSourceInst env program function event.ctx 0 records.first.inst
      (0,entry firstPointer secondPointer,cm) (1,afterFirst firstPointer secondPointer first,cm) :=
    ⟨by simp [records.pos0,blockStart],rfl,by simpa only [records.pos0] using source0⟩
  have prior0 : PendingGuardedScanRel function result event.ctx 0 env program MR
      (ReadEffectFrontier.empty event.ctx env program).history records.first.output.state
      (0,entry firstPointer secondPointer,cm) regs0 world0 := by
    rw [records.firstState]
    simpa only [entryBlock] using related0
  have otherPrior0 : PendingGuardedScanRel function result event.ctx 0 env program MR
      (ReadEffectFrontier.empty event.ctx env program).history records.first.output.state
      (0,entry firstPointer secondPointer,cm) regs0 other0 := by
    rw [records.firstState]
    simpa only [entryBlock,other0] using otherRelated0
  obtain ⟨frontier1,run0,related1,otherRelated1,history1,retained1,pending1,retiredMarks1,retiredValues1⟩ :=
    stock_lower_sunk_paired_frontier_step (isem := isem) run scope dominated events member0 records.marked0
      (bi := 0) (j := 0) (stm := ⟨[63],.atomicLoad .i8 {} 7⟩) blockAt (by decide) (by simp [records.pos0,blockStart]) indexed0 history0
      (by intro captured member;cases member)
      (by rw [records.firstState];exact pending0) (by rw [records.firstState];exact retiredMarks0)
      (by rw [records.firstState];exact retiredValues0) prior0 otherPrior0
  have indexed1 : IndexedSourceInst env program function event.ctx 0 records.second.inst
      (1,afterFirst firstPointer secondPointer first,cm) (2,afterSecond firstPointer secondPointer first second,cm) :=
    ⟨by simp [records.pos1,blockStart],rfl,by simpa only [records.pos1] using source1⟩
  obtain ⟨frontier2,run1,related2,otherRelated2,history2,retained2,pending2,retiredMarks2,retiredValues2⟩ :=
    stock_lower_sunk_paired_frontier_step (isem := isem) run scope dominated events member1 records.marked1
      (bi := 0) (j := 1) (stm := ⟨[64],.atomicLoad .i8 {} 31⟩) blockAt (by decide) (by simp [records.pos1,blockStart]) indexed1 history1 retained1
      (by rw [records.secondState];exact pending1) (by rw [records.secondState];exact retiredMarks1)
      (by rw [records.secondState];exact retiredValues1) (by rw [records.secondState];exact related1) (by rw [records.secondState];exact otherRelated1)
  obtain ⟨R0,consume0⟩ := stock_lower_acquire_consumer_paired_frontier_step run scope dominated events member2 records.recorded0 records.emitted0 records.selected0
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
  have actualOtherRelated2 : PendingGuardedScanRel function result event.ctx event.block env program MR frontier2.history
      records.consumer0.output.state (R0.consumerIndex,afterSecond firstPointer secondPointer first second,cm) regs0 other0 := by
    rw [entryBlock,ci0,records.consumer0State]
    exact otherRelated2
  obtain ⟨frontier3,regs3,world3,other3,run2,related3,otherRelated3,worlds3,history3,retained3,pending3,retiredMarks3,retiredValues3⟩ :=
    consume0 env program (entry firstPointer secondPointer,cm) (afterSecond firstPointer secondPointer first second,cm)
      (afterConsumer0 firstPointer secondPointer first second,cm) body0 (by simpa only [records.pos2] using source2)
      F (Zof F D cm) sb syms isem MR (fun _ h => Or.inl h) stable memorySem memoryOk frontier2 regs0 world0 other0 actualHistory2
      (by rw [records.consumer0State];exact pending2) (by rw [records.consumer0State];exact retiredMarks2)
      (by rw [records.consumer0State];exact retiredValues2) actualRelated2 actualOtherRelated2 memory.2.2
  obtain ⟨R1,consume1⟩ := stock_lower_acquire_consumer_paired_frontier_step run scope dominated events member3 records.recorded1 records.emitted1 records.selected1
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
  have actualOtherRelated3 : PendingGuardedScanRel function result event.ctx event.block env program MR frontier3.history
      records.consumer1.output.state (R1.consumerIndex,afterConsumer0 firstPointer secondPointer first second,cm) regs3 other3 := by
    rw [records.consumer1State,ci1]
    simpa only [ci0] using otherRelated3
  obtain ⟨frontier4,regs4,world4,other4,run3,related4,otherRelated4,worlds4,history4,retained4,pending4,retiredMarks4,retiredValues4⟩ :=
    consume1 env program (entry firstPointer secondPointer,cm) (afterConsumer0 firstPointer secondPointer first second,cm)
      (afterConsumer1 firstPointer secondPointer first second,cm) body1 (by simpa only [records.pos3] using source3)
      F (Zof F D cm) sb syms isem MR (fun _ h => Or.inl h) stable memorySem memoryOk frontier3 regs3 world3 other3 actualHistory3
      (by rw [records.consumer1State];exact pending3) (by rw [records.consumer1State];exact retiredMarks3)
      (by rw [records.consumer1State];exact retiredValues3) actualRelated3 actualOtherRelated3 worlds3
  have actualHistory4 : SourceReadCaptures event.ctx env program (event.output.records.reverse.take 4)
      (entry firstPointer secondPointer,cm) (afterConsumer1 firstPointer secondPointer first second,cm) frontier4.history := by
    simpa only [ci1,records.parts,List.take_succ_cons,List.take_zero,List.nil_append,List.cons_append,List.append_nil] using history4
  have finalRelated : PendingGuardedScanRel function result event.ctx event.block env program MR frontier4.history
      records.terminal.output.state (4,afterConsumer1 firstPointer secondPointer first second,cm) regs4 world4 := by
    rw [records.terminalState]
    simpa only [ci1] using related4
  have recovered := two_load_completed_guarded_recovery run scope events entryBlock records actualHistory4
    (by rw [records.terminalState];exact pending4) (by rw [records.terminalState];exact retiredValues4) finalRelated
  have finalOtherRelated : PendingGuardedScanRel function result event.ctx event.block env program MR frontier4.history
      records.terminal.output.state (4,afterConsumer1 firstPointer secondPointer first second,cm) regs4 other4 := by
    rw [records.terminalState]
    simpa only [ci1] using otherRelated4
  have otherRecovered := two_load_completed_guarded_recovery run scope events entryBlock records actualHistory4
    (by rw [records.terminalState];exact pending4) (by rw [records.terminalState];exact retiredValues4) finalOtherRelated
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
    records.consumer1.output.emitted.toList.map (·.mapRegs resolve),after.toList,regs4,world4,other4,located,?_,?_,recovered,otherRecovered,worlds4⟩
  · simp only [pieces,eventCode,Array.map_append,Array.toList_append,Array.toList_map,List.append_assoc,resolve]
  · exact seqRun_append_fall' (pairSem isem) (seqRun_append_fall' (pairSem isem) preludeRun run2) run3

end Backend.Stock.Proof.AcquireTwoLoadPrefix
