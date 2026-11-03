import FV.Backend.Proof.StockAcquireTwoLoadEntryCapture
import FV.Backend.Proof.StockAcquireSunkFrozenFrontier

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual source-slot identity selects the first retained record uniquely. -/
theorem actual_first_record {event : BlockScanEvent} (schedule : ActualSchedule event)
    {record : ScanRecord} (member : record ∈ event.output.records) (position : record.inst = 0) :
    event.output.records.reverse[0]! = record := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  have actual := List.mem_reverse.mpr member
  rw [parts] at actual
  simp only [List.mem_cons,List.not_mem_nil,or_false] at actual
  rcases actual with equal | equal | equal | equal | equal
  · subst record
    simp only [parts,List.getElem!_cons_zero]
  · subst record;omega
  · subst record;omega
  · subst record;omega
  · subst record;omega

/-- The actual first acquire executes before the second original load fault.
ABI entry constructs the history. The second producer's sunk record evaluates no source instruction. -/
theorem two_load_first_acquire_before_second_fault {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame} (entered : SourceEntry function args frame)
    {env : Clif.Env} {program : Clif.Program} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (source : SourceInstResult env program event.ctx 0 (frame,cm) atFault)
    (failed : SourceInstFault env program event.ctx 1 atFault code)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F function.sig args world) :
    ∃ (consumer : ScanRecord) (block : VBlock) (prelude suffix : Array MInst)
      (regs nextRegs : Nat → CV) (preWorld nextWorld : Arm.ArmState)
      (frontier : ReadEffectFrontier event.ctx env program),
      consumer ∈ event.output.records ∧ consumer.inst = 2 ∧
      result.code.blocks[0]? = some block ∧
      block.insts = prelude++event.output.code.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++suffix ∧
      seqRun isem prelude.toList (entrySeed event.ctx frame) world = some (.fall regs preWorld) ∧
      SameWorld F preWorld world ∧
      seqRun isem (consumer.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs preWorld =
          some (.fall nextRegs nextWorld) ∧ SameWorld F nextWorld preWorld ∧
      SourceInstFault env program event.ctx 1 atFault code ∧
      SourceReadCaptures event.ctx env program (event.output.records.reverse.take 1) (frame,cm) atFault frontier.history ∧
      PendingReadMarks frontier consumer.input ∧ RetiredReadUnmarked frontier consumer.input ∧
      RetiredUndemanded frontier consumer.input ∧
      PendingGuardedScanRel function result event.ctx 0 env program MR frontier.history consumer.input (1,atFault) nextRegs nextWorld := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  obtain ⟨capturedRecord,block,prelude,suffix,regs,preWorld,frontier,firstMember,firstPosition,located,pieces,preludeRun,
    preludeWorld,firstRun,history,retained,pending,retiredMarks,retiredValues,related⟩ :=
    two_load_entry_first_capture run scope dominated size events schedule entered source driver memorySem stable memory arguments
  have firstEq : first = capturedRecord := by
    have actual := actual_first_record schedule firstMember firstPosition
    simpa only [parts,List.getElem!_cons_zero] using actual
  subst capturedRecord
  have secondMember : second ∈ event.output.records := by
    apply List.mem_reverse.mp
    rw [parts]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have consumerMember : consumer0 ∈ event.output.records := by
    apply List.mem_reverse.mp
    rw [parts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rcases schedule with ⟨eventBlock,indices,state0,state1,state2,state3,state4,mark0,mark1,root0,root1,emitted0,emitted1⟩
  have secondState : second.output.state = first.input := by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state1
  have consumerState : consumer0.output.state = second.input := by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state2
  have secondMarked : second.input.sunk[second.inst]! = true := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ,pos1] using mark1
  have beforeRelated : PendingGuardedScanRel function result event.ctx event.block env program MR frontier.history
      second.output.state (1,atFault) regs preWorld := by rw [eventBlock,secondState];exact related
  have beforePending : PendingReadMarks frontier second.output.state := by rw [secondState];exact pending
  have beforeRetiredMarks : RetiredReadUnmarked frontier second.output.state := by rw [secondState];exact retiredMarks
  have beforeRetiredValues : RetiredUndemanded frontier second.output.state := by rw [secondState];exact retiredValues
  obtain ⟨secondEqual,secondRun,afterRelated,afterPending,afterRetiredMarks,afterRetiredValues⟩ :=
    stock_lower_sunk_frozen_frontier_step run events secondMember secondMarked beforeRelated beforePending beforeRetiredMarks beforeRetiredValues
      (isem := isem)
  have actualRoot : consumer0.output.step.map (·.rules.getLast?) = some (some 810) := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using root0
  have actualEmitted : consumer0.output.step.map (·.decision) = some .emitted := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using emitted0
  obtain ⟨step,recorded,selected,emitted⟩ : ∃ step,consumer0.output.step = some step ∧ step.rules.getLast? = some 810 ∧ step.decision = .emitted := by
    cases found : consumer0.output.step with
    | none => simp only [found,Option.map_none] at actualRoot;cases actualRoot
    | some step =>
      exact ⟨step,rfl,Option.some.inj (by simpa only [found,Option.map_some] using actualRoot),
        Option.some.inj (by simpa only [found,Option.map_some] using actualEmitted)⟩
  obtain ⟨R,execute⟩ := stock_lower_acquire_read_before_later_fault run scope dominated events consumerMember recorded emitted selected
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := first_consumer_endpoints eventBlock pos2 R
  have actualHistory : SourceReadCaptures event.ctx env program (event.output.records.reverse.take 1)
      (frame,cm) atFault frontier.history := by simpa only [parts,List.take_succ_cons,List.take_zero] using history
  have body : frame.body = R.block.body := by
    obtain ⟨entry,slots,entryAt,argTypes,paramTypes,assigned,frameEq⟩ := entered
    have entryEq : entry = function.blocks[0]! := by
      simpa [Clif.Function.entry?,function] using entryAt.symm
    have blockAt := R.blockAt
    rw [eventBlock] at blockAt
    have originalAt : function.blocks[0]? = some function.blocks[0]! := by decide
    have blockEq := Option.some.inj (originalAt.symm.trans blockAt)
    rw [frameEq,entryEq,blockEq]
  have prefixFailed : SourceInstFault env program event.ctx (blockStart function event.block+1) atFault code := by
    simpa only [eventBlock,blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using failed
  have consumerRelated : PendingGuardedScanRel function result event.ctx event.block env program MR frontier.history
      consumer0.output.state (1,atFault) regs preWorld := by rw [consumerState];exact afterRelated
  have consumerPending : PendingReadMarks frontier consumer0.output.state := by rw [consumerState];exact afterPending
  have consumerRetiredMarks : RetiredReadUnmarked frontier consumer0.output.state := by rw [consumerState];exact afterRetiredMarks
  have consumerRetiredValues : RetiredUndemanded frontier consumer0.output.state := by rw [consumerState];exact afterRetiredValues
  obtain ⟨capture,remaining,head,nextRegs,nextWorld,producerEq,executed,same,fault,post,pendingAfter,retiredMarksAfter,retiredValuesAfter⟩ :=
    execute env program (frame,cm) atFault 1 code body (by omega) (by omega) prefixFailed F sb syms isem MR stable memorySem memoryOk
      frontier regs preWorld actualHistory consumerPending consumerRetiredMarks consumerRetiredValues consumerRelated
  refine ⟨consumer0,block,prelude,suffix,regs,nextRegs,preWorld,nextWorld,frontier.retire capture remaining head,consumerMember,pos2,located,pieces,preludeRun,preludeWorld,executed,same,
    failed,?_,pendingAfter,retiredMarksAfter,retiredValuesAfter,?_⟩
  · exact actualHistory
  · simpa only [eventBlock] using post

end Backend.Stock.Proof.AcquireTwoLoadPrefix
