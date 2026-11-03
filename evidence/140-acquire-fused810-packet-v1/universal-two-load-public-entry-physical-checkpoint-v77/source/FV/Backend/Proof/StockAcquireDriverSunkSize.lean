import FV.Backend.Proof.StockAcquireMarkedQueue

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerNode

/-- Every exact sink fold preserves the extent of the mark array. -/
theorem sunk_fold_size (bits : Array Bool) (pending : List Nat) :
    (pending.foldl (fun state producer => state.set! producer true) bits).size = bits.size := by
  induction pending generalizing bits with
  | nil => rfl
  | cons producer pending ih => rw [List.foldl_cons,ih];simp

def DriverSunkSize (cap : Nat) (state : DriverState) : Prop :=
  state.state.sunk.size = cap ∧ ∀ event ∈ state.blockScans.toList,event.input.sunk.size = cap

/-- Actual node callbacks preserve the common mark extent and derive each new block entry extent. -/
theorem stock_lower_actual_node_sunk_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {label cap : Nat} {input output : DriverState}
    (called : lowerNode result.ctx ranges order f params label input = .ok output)
    (kept : ∀ event ∈ output.blockScans.toList,event ∈ result.blockScans.toList)
    (prior : DriverSunkSize cap input) : DriverSunkSize cap output := by
  rcases lowerNode_mark_origin called with unchanged | ⟨bi,data,core,coreRun,state,scans⟩
  · refine ⟨?_,?_⟩
    · rw [unchanged.1];exact prior.1
    · intro event member
      apply prior.2 event
      rwa [unchanged.2] at member
  · have member : core.scan ∈ output.blockScans.toList := by rw [scans];simp
    have frame := blockCore_scan_input_sunk coreRun
    obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run (kept core.scan member)
    have entry : core.scan.input.sunk.size = cap := by rw [frame.1];exact prior.1
    refine ⟨?_,?_⟩
    · rw [state,frame.2,exactSunk,sunk_fold_size]
      exact entry
    · intro event present
      rw [scans,Array.toList_push] at present
      rcases List.mem_append.mp present with inherited | current
      · exact prior.2 event inherited
      · have equal := List.mem_singleton.mp current
        rw [equal]
        exact entry

/-- The complete actual traversal derives all inherited mark extents internally. -/
theorem stock_lower_actual_nodes_sunk_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {ranges : Array (Nat × Nat)} {order : Order}
    {params labels : List Nat} {cap : Nat} {input output : DriverState}
    (folded : labels.foldlM (fun state label => lowerNode result.ctx ranges order f params label state) input = .ok output)
    (kept : ∀ event ∈ output.blockScans.toList,event ∈ result.blockScans.toList)
    (prior : DriverSunkSize cap input) : DriverSunkSize cap output := by
  induction labels generalizing input with
  | nil => cases folded;exact prior
  | cons label labels ih =>
    rw [List.foldlM_cons] at folded
    obtain ⟨middle,called,tail⟩ := Except.bind_ok folded
    have middleKept : ∀ event ∈ middle.blockScans.toList,event ∈ result.blockScans.toList :=
      fun event member => kept event (lowerNodes_blockScans_keep tail event member)
    exact ih tail (stock_lower_actual_node_sunk_size run called middleKept prior)

/-- Whole Stock lowering fixes every final and block-entry mark extent to the real initializer. -/
theorem stock_lower_sunk_extents {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    result.final.sunk.size = result.initial.sunk.size ∧
      ∀ event ∈ result.blockScans.toList,event.input.sunk.size = result.initial.sunk.size := by
  have actualRun := run
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : DriverSunkSize built.2.2.sunk.size {
      state := built.2.2,blocks := Array.replicate order.nodes.size default,
      edgeArgs := Array.replicate order.nodes.size #[],schedule := #[],scans := #[],blockScans := #[],rules := #[] } := by
    exact ⟨rfl,by simp⟩
  exact stock_lower_actual_nodes_sunk_size actualRun hdriver (fun event member => member) initial

/-- Every actual retained input inherits the real initializer's mark extent. -/
theorem stock_lower_record_sunk_extent {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    record.input.sunk.size = result.initial.sunk.size := by
  obtain ⟨pending,exactSunk,frames,origin⟩ := stock_lower_record_marked_read_provenance run events records
  rw [exactSunk,sunk_fold_size]
  exact (stock_lower_sunk_extents run).2 event events

end Backend.Stock.Proof.Acquire810
