import FV.Backend.Proof.StockAcquireNodeMarkOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerNode

/-- Every successful node retains all earlier actual scan events. -/
theorem lowerNode_blockScans_keep {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (event : BlockScanEvent) (member : event ∈ input.blockScans.toList) : event ∈ output.blockScans.toList := by
  rcases lowerNode_mark_origin run with unchanged | ⟨bi,data,core,coreRun,state,scans⟩
  · rwa [unchanged.2]
  · rw [scans,Array.toList_push]
    exact List.mem_append_left _ member

/-- Complete actual traversal retains the same earlier events. -/
theorem lowerNodes_blockScans_keep {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun state label => lowerNode ctx ranges order f params label state) input = .ok output) :
    ∀ event ∈ input.blockScans.toList,event ∈ output.blockScans.toList := by
  induction labels generalizing input with
  | nil => cases run; intro event member; exact member
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases called : lowerNode ctx ranges order f params label input with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [called,bind,Except.bind] at run
      intro event member
      exact ih run event (lowerNode_blockScans_keep called event member)

/-- Actual driver states retain source read frames for their state and every recorded block entry. -/
def DriverReadMarked (ctx : Ctx) (state : DriverState) : Prop :=
  ReadMarked ctx state.state ∧ ∀ event ∈ state.blockScans.toList,ReadMarked ctx event.input

/-- An actual node derives inherited entry-mark frames from its real predecessor state and core. -/
theorem stock_lower_actual_node_read_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {label : Nat} {input output : DriverState}
    (called : lowerNode result.ctx ranges order f params label input = .ok output)
    (kept : ∀ event ∈ output.blockScans.toList,event ∈ result.blockScans.toList)
    (prior : DriverReadMarked result.ctx input) : DriverReadMarked result.ctx output := by
  rcases lowerNode_mark_origin called with unchanged | ⟨bi,data,core,coreRun,state,scans⟩
  · refine ⟨prior.1.of_sunk_eq unchanged.1,?_⟩
    intro event member
    apply prior.2 event
    rwa [unchanged.2] at member
  · have member : core.scan ∈ output.blockScans.toList := by rw [scans]; simp
    have frames := stock_lower_actual_core_read_marked run scope coreRun (kept core.scan member) prior.1
    refine ⟨?_,?_⟩
    · rw [state]
      exact frames.1
    · intro event member
      rw [scans,Array.toList_push] at member
      rcases List.mem_append.mp member with inherited | current
      · exact prior.2 event inherited
      · have equal := List.mem_singleton.mp current
        rw [equal]
        exact frames.2

/-- The actual full traversal derives every inherited block-entry read frame internally. -/
theorem stock_lower_actual_nodes_read_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {ranges : Array (Nat × Nat)} {order : Order}
    {params : List Nat} {labels : List Nat} {input output : DriverState}
    (folded : labels.foldlM (fun state label => lowerNode result.ctx ranges order f params label state) input = .ok output)
    (kept : ∀ event ∈ output.blockScans.toList,event ∈ result.blockScans.toList)
    (prior : DriverReadMarked result.ctx input) : DriverReadMarked result.ctx output := by
  induction labels generalizing input with
  | nil => cases folded; exact prior
  | cons label labels ih =>
    rw [List.foldlM_cons] at folded
    cases called : lowerNode result.ctx ranges order f params label input with
    | error message => simp only [called,bind,Except.bind] at folded; cases folded
    | ok middle =>
      simp only [called,bind,Except.bind] at folded
      have middleKept : ∀ event ∈ middle.blockScans.toList,event ∈ result.blockScans.toList :=
        fun event member => kept event (lowerNodes_blockScans_keep folded event member)
      have next := stock_lower_actual_node_read_marked run scope called middleKept prior
      exact ih folded kept next

end Backend.Stock.Proof.Acquire810
