import FV.Backend.Proof.StockAcquirePriorReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Exact mark folds preserve every slot absent from their derived pending list. -/
theorem sunk_fold_absent (bits : Array Bool) (pending : List Nat) (target : Nat)
    (absent : target ∉ pending) :
    (pending.foldl (fun bits producer => bits.set! producer true) bits)[target]! = bits[target]! := by
  induction pending generalizing bits with
  | nil => rfl
  | cons producer rest ih =>
    have different : producer ≠ target := by intro same; exact absent (by simp [same])
    have tailAbsent : target ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
    rw [List.foldl_cons,ih _ tailAbsent]
    exact Array.getElem!_set!_ne _ _ _ _ different

/-- Every true sunk slot comes from the original frontier or an actual sink in the derived list. -/
theorem sunk_fold_marked (bits : Array Bool) (pending : List Nat) (target : Nat)
    (marked : (pending.foldl (fun bits producer => bits.set! producer true) bits)[target]! = true) :
    bits[target]! = true ∨ target ∈ pending := by
  by_cases member : target ∈ pending
  · exact Or.inr member
  · exact Or.inl ((sunk_fold_absent bits pending target member).symm.trans marked)

/-- Earlier actual records account for every new mark before the retained record. -/
theorem stock_lower_record_marked_read_provenance {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ pending : List Nat,
      record.input.sunk = pending.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      (∀ producer ∈ pending,SourceReadFrame event.ctx producer) ∧
      ∀ target,record.input.sunk[target]! = true → event.input.sunk[target]! = true ∨ target ∈ pending := by
  obtain ⟨indices,scan,suffix,groups,prefixRun,boundary,parts,frontiers,exactSunk,frames⟩ :=
    stock_lower_record_prior_read_frontier run events records
  refine ⟨groups.flatten,exactSunk,frames,?_⟩
  intro target marked
  rw [exactSunk] at marked
  exact sunk_fold_marked _ _ _ marked

/-- A mark before an actual record is inherited from block entry or names a classified source read. -/
theorem stock_lower_record_marked_read_or_entry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (target : Nat) (marked : record.input.sunk[target]! = true) :
    event.input.sunk[target]! = true ∨ SourceReadFrame event.ctx target := by
  obtain ⟨pending,exactSunk,frames,provenance⟩ := stock_lower_record_marked_read_provenance run events records
  rcases provenance target marked with inherited | member
  · exact Or.inl inherited
  · exact Or.inr (frames target member)

end Backend.Stock.Proof.Acquire810
