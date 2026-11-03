import FV.Backend.Proof.StockAcquireTwoLoadReturnedFrontier
import FV.Backend.Proof.StockAcquireTwoLoadReturnFacts
import FV.Backend.Proof.StockReturnContract

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual final bindings execute the real return record and preserve the original free/leave result. -/
theorem two_load_returned_runOkABI {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (abi : sigAbiOk function.sig = true) (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {first second : BitVec 8}
    (read0 : cm.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : cm.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (driver : DriverSem isem)
    {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR [] cm world)
    (arguments : ArgsAtEntry F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world) :
    RunOkABI function result.code isem MR [] ⟨0,0,entrySeed event.ctx (entry firstPointer secondPointer),world⟩
      (.returned [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] (cm.free []).leave) := by
  obtain ⟨records,block,prefixCode,suffix,regs,nextWorld,located,pieces,executed,related⟩ :=
    two_load_returned_frontier (env := env) (program := program) run scope dominated size events schedule read0 read1 driver memorySem stable memoryOk memory arguments
  obtain ⟨func,dfg,heldMemory,heldValues⟩ := related
  have blockAt : function.blocks[event.block]? = some function.blocks[0]! := by rw [schedule.1];decide
  have ret : function.blocks[0]!.term = .ret [100,101] := rfl
  have terminalMember := records.member records.terminal (by simp)
  have terminalIndex := actual_terminal_index run scope events schedule.1 records
  let sourceState : Clif.State := ⟨afterConsumer1 firstPointer secondPointer first second,[],cm⟩
  have sourceDefined := actual_returned_source_defined run scope dominated events schedule env program firstPointer secondPointer cm first second read0 read1
  have done := source_return_term_done env program firstPointer secondPointer cm first second
  obtain ⟨step,rs,ps,extra,recorded,emitted,termCode,remaining⟩ :=
    stock_lower_return_record_source_run_auto run scope dominated abi events blockAt ret terminalMember terminalIndex
      (s := sourceState) rfl rfl done sourceDefined heldValues refines stable
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  let termCodeResolved := records.terminal.output.emitted.toList.map (·.mapRegs resolve)
  have decomposition : block.insts.toList = prefixCode++(termCodeResolved++suffix) := by
    simpa only [List.append_assoc,termCodeResolved,resolve] using pieces
  have termSegment : SegAt block prefixCode.length termCodeResolved := by
    intro k bounded
    rw [← Array.getElem?_toList,decomposition,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
      List.getElem?_append_left bounded,List.getElem?_eq_getElem bounded]
  have prefixSegment : SegAt block 0 prefixCode := by
    intro k bounded
    rw [Nat.zero_add,← Array.getElem?_toList,decomposition,List.getElem?_append_left bounded,List.getElem?_eq_getElem bounded]
  have nonempty : 0 < termCodeResolved.length := by
    change 0 < (records.terminal.output.emitted.toList.map (·.mapRegs resolve)).length
    rw [List.length_map,Array.length_toList,termCode]
    change 0 < 1
    exact Nat.zero_lt_succ 0
  have room : 0+prefixCode.length < block.insts.size := by
    have sizes := congrArg List.length decomposition
    simp only [Array.length_toList,List.length_append] at sizes
    omega
  have path := seqRun_fall_star (vc := result.code) (sem := isem) located prefixSegment room executed
  have finished := stock_lower_return_record_runOk run scope dominated abi events blockAt ret terminalMember terminalIndex
    (s := sourceState) rfl rfl done sourceDefined heldValues refines stable located termSegment nextWorld heldMemory
  have sourceSlots : sourceState.frame.slots = [] := rfl
  rw [sourceSlots] at finished
  apply RunOkABI.prefix path
  simpa only [Nat.zero_add] using finished

end Backend.Stock.Proof.AcquireTwoLoadPrefix
