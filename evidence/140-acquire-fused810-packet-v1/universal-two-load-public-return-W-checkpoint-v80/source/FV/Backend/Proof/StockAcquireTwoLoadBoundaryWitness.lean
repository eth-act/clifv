import FV.Backend.Proof.StockAcquireTwoLoadBoundary

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- The unchanged admitted two-load input derives its actual second acquire boundary internally.
The original source outcomes and machine relations remain explicit execution premises. -/
-- witness: native_decide
theorem original_two_load_acquire_boundary :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ event ∈ result.blockScans.toList ∧
      ∀ {args : List Clif.Val} {cm : Clif.Mem} {frame : Clif.Frame} (entered : SourceEntry function args frame)
    {env : Clif.Env} {program : Clif.Program} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (source : SourceInstResult env program event.ctx 0 (frame,cm) atFault)
    (failed : SourceInstFault env program event.ctx 1 atFault code)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR frame.slots cm world) (arguments : ArgsAtEntry F function.sig args world)
    (callers : List (Clif.Frame × List Clif.ValueId)) (mp : ArmFault.MemMap)
    (faults : E2E.MapFaults mp env program ⟨frame,callers,cm⟩),
    VAcquireBoundaryFrom result.code isem ⟨0,0,entrySeed event.ctx frame,world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  obtain ⟨result,event,run,scope,dominated,abi,size,events,schedule⟩ := original_two_load_schedule
  refine ⟨result,event,run,scope,dominated,events,?_⟩
  intro args cm frame entered env program atFault code source failed isem driver F sb syms memorySem MR stable memoryOk world memory arguments callers mp faults
  exact two_load_actual_acquire_boundary run scope dominated size events schedule entered source failed driver memorySem stable memoryOk memory arguments callers mp faults

end Backend.Stock.Proof.AcquireTwoLoadPrefix
