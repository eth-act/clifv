import FV.Backend.Proof.StockAcquireTwoLoadFirstConsumerView
import FV.Backend.Proof.StockAcquireTwoLoadOriginalSource
import FV.Backend.Proof.StockAcquireActualPrefixBoundary

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual ABI entry reaches the first acquire fault without evaluating either source consumer or the second load. -/
theorem two_load_first_fault_boundary {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {code : Clif.TrapCode}
    (failed : cm.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .trap code)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {world : Arm.ArmState} (memory : MR [] cm world)
    (arguments : ArgsAtEntry F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world)
    (callers : List (Clif.Frame × List Clif.ValueId)) (mp : ArmFault.MemMap)
    (faults : MapFaults mp env program ⟨entry firstPointer secondPointer,callers,cm⟩) :
    VAcquireBoundaryFrom result.code isem ⟨0,0,entrySeed event.ctx (entry firstPointer secondPointer),world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  obtain ⟨consumer,step,suffixCode,member,position,recorded,selected,emitted,stateEq,codeEq⟩ := actual_first_consumer_view run events schedule
  obtain ⟨entryEvent,block,prelude,after,regs,nextWorld,entryEvents,entryBlock,located,pieces,executed,same,initial⟩ :=
    stock_lower_entry_pending_frontier run scope dominated (source_entry_pointers firstPointer secondPointer) driver memorySem stable memory arguments
  have eventEq := actual_single_event size entryEvents events
  subst entryEvent
  obtain ⟨R,pointerReg,dest,chunk,transfer⟩ := stock_lower_acquire_fault_chunk run scope dominated events member recorded emitted selected
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := first_consumer_endpoints schedule.1 position R
  have sourceFault := actual_first_source_fault run scope events schedule.1 position R env program firstPointer secondPointer cm code failed
  have actualFault : SourceInstFault env program event.ctx R.producer (entry firstPointer secondPointer,cm) code := by
    rw [producer];exact sourceFault
  obtain ⟨history,pending,retiredMarks,retiredValues,related⟩ := initial env program
  have actualHistory : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.producerIndex)
      (entry firstPointer secondPointer,cm) (entry firstPointer secondPointer,cm) (ReadEffectFrontier.empty event.ctx env program).history := by
    rw [producerIndex,List.take_zero]
    exact history
  have actualPending : PendingReadMarks (ReadEffectFrontier.empty event.ctx env program) consumer.output.state := by rw [stateEq];exact pending
  have actualRetired : RetiredUndemanded (ReadEffectFrontier.empty event.ctx env program) consumer.output.state := by rw [stateEq];exact retiredValues
  have actualRelated : PendingGuardedScanRel function result event.ctx event.block env program MR
      (ReadEffectFrontier.empty event.ctx env program).history consumer.output.state
      (R.producerIndex,entry firstPointer secondPointer,cm) regs nextWorld := by
    rw [producerIndex,stateEq]
    exact related
  obtain ⟨empty,guarded,address,bytes,access,j,bound,unmapped⟩ := transfer env program ⟨entry firstPointer secondPointer,callers,cm⟩
    (entry firstPointer secondPointer,cm) mp code faults actualFault MR (ReadEffectFrontier.empty event.ctx env program) regs nextWorld
    actualHistory actualPending actualRetired actualRelated
  have finalPieces : block.insts.toList = prelude.toList++
      (.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags)::
        (suffixCode.toList.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++after.toList) := by
    simp only [pieces,codeEq,Array.map_append,Array.toList_append,Array.toList_map,chunk,List.append_assoc,List.cons_append,List.nil_append]
  exact acquire_boundary_of_actual_prefix located finalPieces executed access ⟨j,bound,unmapped⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
