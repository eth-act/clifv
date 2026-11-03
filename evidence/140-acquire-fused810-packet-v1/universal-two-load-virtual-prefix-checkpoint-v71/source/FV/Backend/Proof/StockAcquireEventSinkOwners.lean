import FV.Backend.Proof.StockAcquireSinkBlockOwner

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A sink mark belongs to an actual recorded block and its original source event interval. -/
def SinkOwnedBy (f : Clif.Function) (events : List BlockScanEvent) (producer : Nat) : Prop :=
  ∃ owner ∈ events,∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (block : Clif.Block),
    Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[owner.block]? = some block ∧
    some producer ∈ blockColorEvents ranges (block,owner.block)

/-- Retaining earlier actual events retains all their source owners. -/
theorem SinkOwnedBy.of_subset {f : Clif.Function} {before after : List BlockScanEvent} {producer : Nat}
    (owned : SinkOwnedBy f before producer) (keep : ∀ event ∈ before,event ∈ after) : SinkOwnedBy f after producer := by
  obtain ⟨owner,member,original,ranges,initial,block,built,blockAt,source⟩ := owned
  exact ⟨owner,keep owner member,original,ranges,initial,block,built,blockAt,source⟩

/-- An actual complete frontier locates every producer in its real retained record group. -/
theorem ExecutedRecordFrontiers.producer_owner {f : Clif.Function} {ctx : Ctx}
    {records : List ScanRecord} {groups : List (List Nat)} (frontiers : ExecutedRecordFrontiers f ctx records groups)
    {producer : Nat} (member : producer ∈ groups.flatten) :
    ∃ record ∈ records,∃ pending,ExecutedRecordFrontier f ctx record pending ∧ producer ∈ pending := by
  induction frontiers with
  | nil => cases member
  | @cons record pending records groups head tail ih =>
    simp only [List.flatten_cons,List.mem_append] at member
    rcases member with current | rest
    · exact ⟨record,List.mem_cons_self ..,pending,head,current⟩
    · obtain ⟨owner,retained,group,frontier,present⟩ := ih rest
      exact ⟨owner,List.mem_cons_of_mem _ retained,group,frontier,present⟩

/-- Every new mark in the actual scan has this actual block as its original source owner.
Inherited entry marks remain explicit and are not assumed empty. -/
theorem stock_lower_event_sink_owner_delta {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    (producer : Nat) (marked : event.output.state.sunk[producer]! = true) :
    event.input.sunk[producer]! = true ∨ SinkOwnedBy f [event] producer := by
  obtain ⟨groups,frontiers,exactMarks⟩ := stock_lower_event_executed_frontiers run events
  rw [exactMarks] at marked
  rcases sunk_fold_marked event.input.sunk groups.flatten producer marked with inherited | member
  · exact Or.inl inherited
  · obtain ⟨record,retained,pending,frontier,present⟩ := frontiers.producer_owner member
    obtain ⟨original,ranges,initial,block,built,blockAt,sources⟩ :=
      stock_lower_record_sink_block_owner run scope events retained frontier
    exact Or.inr ⟨event,List.mem_singleton_self _,original,ranges,initial,block,built,blockAt,sources producer present⟩

end Backend.Stock.Proof.Acquire810
