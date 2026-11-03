import FV.Backend.Proof.StockAcquireTwoLoadVirtualPrefix
import FV.Backend.Proof.StockAcquireFaultChunk

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual two-load prefix reaches the second acquire with the original fault address unmapped.
The first acquire executes. Every demanded binding is recovered before the second access. -/
theorem two_load_second_fault_after_actual_prefix {result : Result}
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
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F function.sig args world)
    (callers : List (Clif.Frame × List Clif.ValueId)) (mp : ArmFault.MemMap)
    (faults : E2E.MapFaults mp env program ⟨frame,callers,cm⟩) :
    ∃ (consumer : ScanRecord) (block : VBlock) (prefixCode suffix : List MInst)
      (regs : Nat → CV) (nextWorld : Arm.ArmState) (frontier : ReadEffectFrontier event.ctx env program)
      (pointerReg dest : Nat) (ty : CTy) (flags : Clif.MemFlags) (address : BitVec 64) (bytes : Nat),
      consumer ∈ event.output.records ∧ consumer.inst = 3 ∧ result.code.blocks[0]? = some block ∧
      block.insts.toList = prefixCode++[.loadAcquire ty (.vreg dest .int) (.vreg pointerReg .int) flags]++suffix ∧
      seqRun isem prefixCode (entrySeed event.ctx frame) world = some (.fall regs nextWorld) ∧
      SameWorld F nextWorld world ∧ SourceInstFault env program event.ctx 1 atFault code ∧
      frontier.pending = [] ∧
      GuardedScanRel function result event.ctx 0 MR consumer.output.state (1,atFault) regs nextWorld ∧
      AcquireAt (.loadAcquire ty (.vreg dest .int) (.vreg pointerReg .int) flags) [regs pointerReg] nextWorld code address bytes ∧
      ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none := by
  obtain ⟨consumer,block,prefixCode,suffix,regs,nextWorld,frontier,member,position,located,pieces,executed,same,fault,
    history,pending,retiredMarks,retiredValues,related⟩ :=
    two_load_actual_virtual_prefix run scope dominated size events schedule entered source failed driver memorySem stable memoryOk memory arguments
  have eventBlock := schedule.1
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  have actual := List.mem_reverse.mpr member
  rw [parts] at actual
  simp only [List.mem_cons,List.not_mem_nil,or_false] at actual
  have consumerEq : consumer = consumer1 := by
    rcases actual with equal | equal | equal | equal | equal
    · subst consumer;omega
    · subst consumer;omega
    · subst consumer;omega
    · exact equal
    · subst consumer;omega
  subst consumer
  have root : consumer1.output.step.map (·.rules.getLast?) = some (some 810) := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.2.2.2.2.2.1
  have emitted : consumer1.output.step.map (·.decision) = some .emitted := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨step,recorded,selected,emittedStep⟩ : ∃ step,consumer1.output.step = some step ∧ step.rules.getLast? = some 810 ∧ step.decision = .emitted := by
    cases found : consumer1.output.step with
    | none => simp only [found,Option.map_none] at root;cases root
    | some step => exact ⟨step,rfl,Option.some.inj (by simpa only [found,Option.map_some] using root),
        Option.some.inj (by simpa only [found,Option.map_some] using emitted)⟩
  obtain ⟨R,pointerReg,dest,chunk,transfer⟩ := stock_lower_acquire_fault_chunk run scope dominated events member recorded emittedStep selected
  obtain ⟨producerIndex,consumerIndex,producer,value,pointer,ty,flags⟩ := second_consumer_endpoints eventBlock pos3 R
  have actualFault : SourceInstFault env program event.ctx R.producer atFault code := by rw [producer];exact fault
  have actualHistory : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.producerIndex)
      (frame,cm) atFault frontier.history := by rw [producerIndex];exact history
  have actualRelated : PendingGuardedScanRel function result event.ctx event.block env program MR frontier.history
      consumer1.output.state (R.producerIndex,atFault) regs nextWorld := by rw [eventBlock,producerIndex];exact related
  obtain ⟨empty,guarded,address,bytes,access,j,bound,unmapped⟩ := transfer env program ⟨frame,callers,cm⟩ atFault mp code faults actualFault
    MR frontier regs nextWorld actualHistory pending retiredValues actualRelated
  refine ⟨consumer1,block,prefixCode,suffix,regs,nextWorld,frontier,pointerReg,dest,CTy.ofClif R.ty,R.flags,address,bytes,
    member,pos3,located,?_,executed,same,fault,empty,?_,access,j,bound,unmapped⟩
  · rw [← chunk];exact pieces
  · simpa only [eventBlock,producerIndex] using guarded

end Backend.Stock.Proof.AcquireTwoLoadPrefix
