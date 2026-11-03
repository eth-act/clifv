import FV.Backend.Proof.StockAcquireSelectedResolvedFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Exact sink folds retain every earlier actual mark. -/
theorem sunk_fold_keeps_mark (bits : Array Bool) (pending : List Nat) (target : Nat)
    (marked : bits[target]! = true) :
    (pending.foldl (fun state producer => state.set! producer true) bits)[target]! = true := by
  induction pending generalizing bits with
  | nil => exact marked
  | cons producer pending ih =>
    apply ih
    by_cases same : producer = target
    · subst producer
      have inside : target < bits.size := by
        apply Classical.byContradiction
        intro outside
        have absent := Array.getElem?_eq_none (Nat.le_of_not_lt outside)
        simp only [getElem!_def,absent,Option.getD_none] at marked
        cases marked
      simp [Array.set!_eq_setIfInBounds,inside]
    · rw [Array.getElem!_set!_ne _ _ _ _ same]
      exact marked

/-- Every in-bounds member of the complete sink list becomes marked. -/
theorem sunk_fold_marks_member (bits : Array Bool) (pending : List Nat) (target : Nat)
    (inside : target < bits.size) (member : target ∈ pending) :
    (pending.foldl (fun state producer => state.set! producer true) bits)[target]! = true := by
  induction pending generalizing bits with
  | nil => cases member
  | cons producer pending ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst producer
      exact sunk_fold_keeps_mark (bits.set! target true) pending target (by simp [Array.set!_eq_setIfInBounds,inside])
    · apply ih (bits := bits.set! producer true) (by simpa using inside) member

/-- Actual interpreter traces mark every in-bounds deferred producer. -/
theorem PendingMarks.member_marked {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) {producer : Nat}
    (inside : producer < before.sunk.size) (member : producer ∈ pending) : after.sunk[producer]! = true := by
  rw [trace.sunk_exact]
  exact sunk_fold_marks_member _ _ _ inside member

/-- Each real frontier preserves earlier queue marks and installs its entire new pending group. -/
theorem RecordFrontier.queue_marks {f : Clif.Function} {ctx : Ctx} {record : ScanRecord}
    {queue pending : List Nat} (frontier : RecordFrontier f ctx record pending)
    (prior : ∀ producer ∈ queue,record.input.sunk[producer]! = true)
    (inside : ∀ producer ∈ pending,producer < record.input.sunk.size) :
    ∀ producer ∈ queue++pending,record.output.state.sunk[producer]! = true := by
  intro producer member
  rw [frontier.1]
  rcases List.mem_append.mp member with inherited | current
  · exact sunk_fold_keeps_mark _ _ _ (prior producer inherited)
  · exact sunk_fold_marks_member _ _ _ (inside producer current) current

end Backend.Stock.Proof.Acquire810
