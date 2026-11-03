import FV.Backend.Proof.StockAcquireTwoLoadFaultPrefix
import FV.Backend.Proof.StockAcquireActualPrefixBoundary

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual ABI entry reaches the second acquire boundary after executing the first acquire.
The original memory mapping supplies its unmapped byte. The source fault frame remains unchanged. -/
theorem two_load_actual_acquire_boundary {result : Result}
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
    VAcquireBoundaryFrom result.code isem ⟨0,0,entrySeed event.ctx frame,world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  obtain ⟨consumer,block,prefixCode,suffix,regs,nextWorld,frontier,pointerReg,dest,ty,flags,address,bytes,
    member,position,located,pieces,executed,same,fault,empty,guarded,access,j,bound,unmapped⟩ :=
    two_load_second_fault_after_actual_prefix run scope dominated size events schedule entered source failed driver memorySem stable
      memoryOk memory arguments callers mp faults
  exact acquire_boundary_of_actual_prefix located (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using pieces)
    executed access ⟨j,bound,unmapped⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
