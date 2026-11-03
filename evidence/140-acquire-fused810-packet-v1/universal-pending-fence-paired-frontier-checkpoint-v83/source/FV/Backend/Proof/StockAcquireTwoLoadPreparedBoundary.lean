import FV.Backend.Proof.StockAcquireTwoLoadBoundary
import FV.Backend.Proof.StockAcquireStage

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 Backend.DeadCleanup E2E
set_option autoImplicit false
set_option Elab.async false

/-- Both actual preparation modes preserve the reached second acquire and its original fault address.
The original GOT relation supplies the valueSemV prefix used by the W allocator transfer. -/
theorem two_load_prepared_acquire_boundary {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame} (entered : SourceEntry function args frame)
    {env : Clif.Env} {program : Clif.Program} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (source : SourceInstResult env program event.ctx 0 (frame,cm) atFault)
    (failed : SourceInstFault env program event.ctx 1 atFault code)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {fc : FnCtx} {X : ExtSem} (slot : fc.slotBase = sb)
    (symbols : ∀ name address,syms name = some address → X.sym name 0 = BitVec.ofNat 64 address)
    {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F function.sig args world)
    (callers : List (Clif.Frame × List Clif.ValueId)) (mp : ArmFault.MemMap)
    (faults : E2E.MapFaults mp env program ⟨frame,callers,cm⟩)
    {cleanup : Bool} {prepared : VCode}
    (preparedCheck : prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true) :
    VAcquireBoundaryFrom prepared (valueSemV (GotV prepared) F fc X) ⟨0,0,entrySeed event.ctx frame,world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  apply acquireTrap_gotV_value
  apply acquireTrap_stage preparedCheck
  exact two_load_actual_acquire_boundary run scope dominated size events schedule entered source failed
    (driverSem_valueSem F fc X) (memRefines_valueSem F fc X slot symbols) stable memoryOk memory arguments callers mp faults

end Backend.Stock.Proof.AcquireTwoLoadPrefix
