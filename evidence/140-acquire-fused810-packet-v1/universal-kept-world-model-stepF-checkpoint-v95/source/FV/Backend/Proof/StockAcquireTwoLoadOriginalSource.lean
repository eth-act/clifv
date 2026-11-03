import FV.Backend.Proof.StockAcquireTwoLoadSourceRelations

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Every pair of original i64 arguments constructs the accepted source entry internally. -/
theorem source_entry_pointers (firstPointer secondPointer : BitVec 64) :
    SourceEntry function [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] (entry firstPointer secondPointer) := by
  refine ⟨function.blocks[0]!, (entry firstPointer secondPointer).regs,rfl,rfl,rfl,?_,rfl⟩
  simp only [function,Clif.Regs.setMany,Clif.Regs.empty,Clif.Regs.set]
  apply congrArg some
  funext value
  by_cases first : value = 7 <;> by_cases second : value = 31 <;> simp_all [entry,Clif.Regs.empty]

/-- The original all-fuel trap partition supplies actual event-context relations in its second-read branch. -/
theorem actual_relations_of_original_second_trap {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (fuel : Nat) (code : Clif.TrapCode)
    (trapped : Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],memory⟩ = .trapped code)
    (firstSucceeded : ∃ raw,memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok raw) :
    ∃ raw,SourceInstResult env program event.ctx 0 (entry firstPointer secondPointer,memory)
      (afterFirst firstPointer secondPointer raw,memory) ∧
      SourceInstFault env program event.ctx 1 (afterFirst firstPointer secondPointer raw,memory) code := by
  obtain ⟨raw,loaded⟩ := firstSucceeded
  rcases (source_first_trap env program firstPointer secondPointer memory fuel code).mp trapped with first | second
  · rw [loaded] at first
    cases first.2
  · obtain ⟨bound,actual,first,failed⟩ := second
    have equal := Clif.Res.ok.inj (first.symm.trans loaded)
    subst actual
    exact ⟨raw,actual_two_load_source_relations run scope dominated events schedule env program firstPointer secondPointer memory raw code loaded failed⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
