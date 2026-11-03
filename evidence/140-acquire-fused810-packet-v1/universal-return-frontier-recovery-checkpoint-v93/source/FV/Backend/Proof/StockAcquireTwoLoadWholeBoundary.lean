import FV.Backend.Proof.StockAcquireTwoLoadFirstFaultBoundary
import FV.Backend.Proof.StockAcquireTwoLoadBoundary

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810 E2E
set_option autoImplicit false
set_option Elab.async false

/-- Every original source trap reaches its actual acquire boundary; neither read-success nor read-fault branch is an input guard. -/
theorem two_load_whole_source_fault_boundary {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    (size : result.blockScans.size = 1) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    {env : Clif.Env} {program : Clif.Program} {firstPointer secondPointer : BitVec 64}
    {cm : Clif.Mem} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],cm⟩ = .trapped code)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms function MR)
    {world : Arm.ArmState} (memory : MR [] cm world)
    (arguments : ArgsAtEntry F function.sig [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] world)
    (callers : List (Clif.Frame × List Clif.ValueId)) (mp : ArmFault.MemMap)
    (faults : MapFaults mp env program ⟨entry firstPointer secondPointer,callers,cm⟩) :
    VAcquireBoundaryFrom result.code isem ⟨0,0,entrySeed event.ctx (entry firstPointer secondPointer),world⟩ code
      (fun address bytes => ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) := by
  rcases (source_first_trap env program firstPointer secondPointer cm fuel code).mp trapped with first | second
  · exact two_load_first_fault_boundary run scope dominated size events schedule first.2 driver memorySem stable memory arguments callers mp faults
  · obtain ⟨bound,raw,loaded,failed⟩ := second
    obtain ⟨source,fault⟩ := actual_two_load_source_relations run scope dominated events schedule env program firstPointer secondPointer cm raw code loaded failed
    exact two_load_actual_acquire_boundary run scope dominated size events schedule (source_entry_pointers firstPointer secondPointer)
      source fault driver memorySem stable memoryOk memory arguments callers mp faults

end Backend.Stock.Proof.AcquireTwoLoadPrefix
