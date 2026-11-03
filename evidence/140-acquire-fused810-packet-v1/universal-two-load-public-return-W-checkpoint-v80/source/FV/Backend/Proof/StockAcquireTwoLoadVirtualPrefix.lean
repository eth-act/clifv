import FV.Backend.Proof.StockAcquireTwoLoadMixedPrefix

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The prelude and first acquire form the actual virtual prefixCode before the second acquire.
The source fault stays fixed while both sunk producer chunks emit no instructions. -/
theorem two_load_actual_virtual_prefix {result : Result}
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
    ∃ (consumer : ScanRecord) (block : VBlock) (prefixCode suffix : List MInst)
      (regs : Nat → CV) (nextWorld : Arm.ArmState) (frontier : ReadEffectFrontier event.ctx env program),
      consumer ∈ event.output.records ∧ consumer.inst = 3 ∧ result.code.blocks[0]? = some block ∧
      block.insts.toList = prefixCode++consumer.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++suffix ∧
      seqRun isem prefixCode (entrySeed event.ctx frame) world = some (.fall regs nextWorld) ∧
      SameWorld F nextWorld world ∧ SourceInstFault env program event.ctx 1 atFault code ∧
      SourceReadCaptures event.ctx env program (event.output.records.reverse.take 1) (frame,cm) atFault frontier.history ∧
      PendingReadMarks frontier consumer.output.state ∧ RetiredReadUnmarked frontier consumer.output.state ∧
      RetiredUndemanded frontier consumer.output.state ∧
      PendingGuardedScanRel function result event.ctx 0 env program MR frontier.history consumer.output.state (1,atFault) regs nextWorld := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  obtain ⟨actualConsumer,block,prelude,after,regs,nextRegs,preWorld,nextWorld,frontier,member,position,located,pieces,
    preludeRun,preludeWorld,executed,same,fault,history,pending,retiredMarks,retiredValues,related⟩ :=
    two_load_first_acquire_before_second_fault run scope dominated size events schedule entered source failed driver memorySem stable memoryOk memory arguments
  have actual := List.mem_reverse.mpr member
  rw [parts] at actual
  simp only [List.mem_cons,List.not_mem_nil,or_false] at actual
  have consumerEq : actualConsumer = consumer0 := by
    rcases actual with equal | equal | equal | equal | equal
    · subst actualConsumer;omega
    · subst actualConsumer;omega
    · exact equal
    · subst actualConsumer;omega
    · subst actualConsumer;omega
  subst actualConsumer
  have firstMember : first ∈ event.output.records := by apply List.mem_reverse.mp;rw [parts];exact List.mem_cons_self ..
  have secondMember : second ∈ event.output.records := by apply List.mem_reverse.mp;rw [parts];exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have consumerMember : consumer1 ∈ event.output.records := by
    apply List.mem_reverse.mp;rw [parts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have firstMarked : first.input.sunk[first.inst]! = true := by
    simpa only [parts,List.getElem!_cons_zero,pos0] using schedule.2.2.2.2.2.2.2.1
  have secondMarked : second.input.sunk[second.inst]! = true := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ,pos1] using schedule.2.2.2.2.2.2.2.2.1
  have emptyChunk : ∀ record ∈ event.output.records,record.input.sunk[record.inst]! = true → record.output.emitted = #[] := by
    intro record retained marked
    have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record retained
    exact congrArg Scan.emitted (Except.ok.inj (actual.symm.trans
      (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked)))
  have empty0 := emptyChunk first firstMember firstMarked
  have empty1 := emptyChunk second secondMember secondMarked
  obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run events
  have eventCode : event.output.code = consumer0.output.emitted++consumer1.output.emitted++terminal.output.emitted := by
    apply Array.toList_inj.mp
    simp only [assembly,parts,List.flatMap_cons,List.flatMap_nil,empty0,empty1,Array.toList_empty,
      List.nil_append,List.append_nil,Array.toList_append,List.append_assoc]
  have consumerState : consumer1.output.state = consumer0.input := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.1
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨consumer1,block,prelude.toList++consumer0.output.emitted.toList.map (·.mapRegs resolve),
    terminal.output.emitted.toList.map (·.mapRegs resolve)++after.toList,nextRegs,nextWorld,frontier,consumerMember,pos3,located,?_,
    seqRun_append_fall' isem preludeRun executed,SameWorld.trans same preludeWorld,fault,history,?_,?_,?_,?_⟩
  · simp only [pieces,eventCode,Array.map_append,Array.toList_append,Array.toList_map,List.append_assoc,resolve]
  · rw [consumerState];exact pending
  · rw [consumerState];exact retiredMarks
  · rw [consumerState];exact retiredValues
  · rw [consumerState];exact related

end Backend.Stock.Proof.AcquireTwoLoadPrefix
