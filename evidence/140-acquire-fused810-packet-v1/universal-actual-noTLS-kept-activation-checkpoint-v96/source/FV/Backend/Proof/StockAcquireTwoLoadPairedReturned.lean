import FV.Backend.Proof.StockAcquireTwoLoadPairedFrontier
import FV.Backend.Proof.StockAcquireTwoLoadReturnFacts
import FV.E2E.StockMemoryPairedReturnValue

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Actual paired histories execute the real return with both complete final bindings and original free/leave memory. -/
theorem two_load_returned_paired_runOkABI {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (abi : sigAbiOk function.sig = true) (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {first second : BitVec 8}
    (read0 : cm.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first)
    (read1 : cm.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (tls : XTls Γ.F X)
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {world otherWorld : Arm.ArmState} (memory : MRP Γ function c D [] cm (world,otherWorld))
    (arguments : ArgsAtEntry Γ.F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world)
    (otherArguments : ArgsAtEntry Γ.F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] otherWorld)
    (registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈ (locsOf function.sig).zip [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] →
      regVal otherWorld pin = regVal world pin) :
    RunOkABI function result.code (pairSem (valueSem Γ.F fc X)) (MRP Γ function c D) []
      ⟨0,0,entrySeed event.ctx (entry firstPointer secondPointer),(world,otherWorld)⟩
      (.returned [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] (cm.free []).leave) := by
  let isem := valueSem Γ.F fc X
  have stable := mrStable_relW Γ function c
  have refines := refines_valueSem Γ.F fc X
  obtain ⟨records,block,prefixCode,suffix,regs,nextWorld,nextOther,located,pieces,executed,related,otherRelated,worlds⟩ :=
    two_load_returned_paired_frontier (env := env) (program := program) run scope dominated size events schedule read0 read1
      slot symbols memory arguments otherArguments registers
  have heldValues := related.2.2.2
  have pairedMemory : MRP Γ function c D [] cm (nextWorld,nextOther) := ⟨related.2.2.1,otherRelated.2.2.1,worlds⟩
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
  have path := seqRun_fall_star (vc := result.code) (sem := pairSem isem) located prefixSegment room executed
  have finished := E2E.StockMemory.stock_lower_return_record_paired_runOk_value (fc := fc) run scope dominated abi events blockAt ret terminalMember terminalIndex
    (s := sourceState) rfl rfl done sourceDefined heldValues tls located termSegment (nextWorld,nextOther) pairedMemory
  have sourceSlots : sourceState.frame.slots = [] := rfl
  rw [sourceSlots] at finished
  apply RunOkABI.prefix path
  simpa only [Nat.zero_add] using finished

end Backend.Stock.Proof.AcquireTwoLoadPrefix
