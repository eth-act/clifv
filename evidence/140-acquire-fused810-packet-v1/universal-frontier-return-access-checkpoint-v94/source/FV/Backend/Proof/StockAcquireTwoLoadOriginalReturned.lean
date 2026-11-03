import FV.Backend.Proof.StockAcquireTwoLoadSourceReturned
import FV.Backend.Proof.StockAcquireTwoLoadEntryNormal

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Every original public returned execution supplies both successful reads and its exact values and memory internally. -/
theorem original_returned_reads {args : List Clif.Val} {state : Clif.State}
    (entered : ClifEntry function args state) (env : Clif.Env) (program : Clif.Program) (fuel : Nat)
    {values : List Clif.Val} {final : Clif.Mem}
    (returned : Clif.runLoop env program fuel state = .returned values final) :
    ∃ (firstPointer secondPointer : BitVec 64) (first second : BitVec 8),
      args = [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] ∧ state.frame = entry firstPointer secondPointer ∧
      state.callers = [] ∧
      state.mem.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok first ∧
      state.mem.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .ok second ∧
      values = [⟨.i64,first.setWidth 64⟩,⟨.i64,second.setWidth 64⟩] ∧ final = (state.mem.free []).leave := by
  obtain ⟨firstPointer,secondPointer,arguments,frame,callers⟩ := original_entry_normal_form entered
  have same : (⟨entry firstPointer secondPointer,[],state.mem⟩ : Clif.State) = state := by cases state;simp_all
  have actual : Clif.runLoop env program fuel ⟨entry firstPointer secondPointer,[],state.mem⟩ = .returned values final := by
    rw [same];exact returned
  obtain ⟨bound,first,second,read0,read1,valuesEq,memoryEq⟩ := (source_returned_iff env program firstPointer secondPointer state.mem fuel values final).mp actual
  exact ⟨firstPointer,secondPointer,first,second,arguments,frame,callers,read0,read1,valuesEq,memoryEq⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
