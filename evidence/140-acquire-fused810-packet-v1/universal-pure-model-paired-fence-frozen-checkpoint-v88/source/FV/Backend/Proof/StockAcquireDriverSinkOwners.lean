import FV.Backend.Proof.StockAcquireEventSinkOwners

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerNode

/-- Each recorded entry mark belongs to an actual event recorded before that entry. -/
def EarlierEntryOwners (f : Clif.Function) (events : List BlockScanEvent) : Prop :=
  ∀ event ∈ events,∃ (earlier later : List BlockScanEvent),events = earlier++event::later ∧
    ∀ producer,event.input.sunk[producer]! = true → SinkOwnedBy f earlier producer

/-- Ownership covers the live driver state and every exact earlier block-entry frontier. -/
def DriverSinkOwners (f : Clif.Function) (state : DriverState) : Prop :=
  (∀ producer,state.state.sunk[producer]! = true → SinkOwnedBy f state.blockScans.toList producer) ∧
    EarlierEntryOwners f state.blockScans.toList

/-- The real node transfer propagates inherited ownership and adds only its actual new block owner. -/
theorem stock_lower_actual_node_sink_owners {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {label : Nat} {input output : DriverState}
    (called : lowerNode result.ctx ranges order f params label input = .ok output)
    (kept : ∀ event ∈ output.blockScans.toList,event ∈ result.blockScans.toList)
    (prior : DriverSinkOwners f input) : DriverSinkOwners f output := by
  rcases lowerNode_mark_origin called with unchanged | ⟨bi,data,core,coreRun,state,scans⟩
  · refine ⟨?_,?_⟩
    · intro producer marked
      rw [unchanged.1] at marked
      have owned := prior.1 producer marked
      rwa [unchanged.2]
    · rw [unchanged.2]
      exact prior.2
  · have member : core.scan ∈ output.blockScans.toList := by rw [scans];simp
    have fields := blockCore_scan_input_sunk coreRun
    refine ⟨?_,?_⟩
    · intro producer marked
      rw [state,fields.2] at marked
      rcases stock_lower_event_sink_owner_delta run scope (kept core.scan member) producer marked with inherited | current
      · rw [fields.1] at inherited
        exact (prior.1 producer inherited).of_subset (fun event retained => lowerNode_blockScans_keep called event retained)
      · exact current.of_subset (by intro event present;have same := List.mem_singleton.mp present;rw [same];exact member)
    · intro event retained
      rw [scans,Array.toList_push] at retained ⊢
      rcases List.mem_append.mp retained with old | current
      · obtain ⟨earlier,later,parts,owners⟩ := prior.2 event old
        refine ⟨earlier,later++[core.scan],?_,owners⟩
        rw [parts,List.append_assoc]
        rfl
      · have same := List.mem_singleton.mp current
        subst event
        refine ⟨input.blockScans.toList,[],by simp,?_⟩
        intro producer marked
        rw [fields.1] at marked
        exact prior.1 producer marked

/-- The actual complete traversal derives every live and inherited sink owner. -/
theorem stock_lower_actual_nodes_sink_owners {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {labels : List Nat} {input output : DriverState}
    (folded : labels.foldlM (fun state label => lowerNode result.ctx ranges order f params label state) input = .ok output)
    (kept : ∀ event ∈ output.blockScans.toList,event ∈ result.blockScans.toList)
    (prior : DriverSinkOwners f input) : DriverSinkOwners f output := by
  induction labels generalizing input with
  | nil => cases folded;exact prior
  | cons label labels ih =>
    rw [List.foldlM_cons] at folded
    cases called : lowerNode result.ctx ranges order f params label input with
    | error message => simp only [called,bind,Except.bind] at folded;cases folded
    | ok middle =>
      simp only [called,bind,Except.bind] at folded
      have middleKept : ∀ event ∈ middle.blockScans.toList,event ∈ result.blockScans.toList :=
        fun event member => kept event (lowerNodes_blockScans_keep folded event member)
      have next := stock_lower_actual_node_sink_owners run scope called middleKept prior
      exact ih folded next

end Backend.Stock.Proof.Acquire810
