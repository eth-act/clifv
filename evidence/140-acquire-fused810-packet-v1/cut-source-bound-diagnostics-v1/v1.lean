import FV.Backend.Proof.StockAcquireRecordOutputCut

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Reference resets preserve every strictly earlier source color. -/
theorem referenceCut_fold_above {colors : Array Nat} {floor cut : Nat}
    (ordered : PositiveColorOrder colors) {producer : Nat}
    (positive : colors[producer]! ≠ 0) (floorEq : floor = colors[producer]!)
    (above : floor < cut) (indices : List Nat)
    (earlier : ∀ inst ∈ indices,producer < inst) :
    floor < indices.foldl (referenceCut colors) cut := by
  induction indices generalizing cut with
  | nil => exact above
  | cons inst indices ih =>
    apply ih
    · unfold referenceCut
      split
      · exact above
      · rename_i nonzero
        rw [floorEq]
        exact ordered producer inst positive nonzero (earlier inst (List.mem_cons_self ..))
    · intro target member
      exact earlier target (List.mem_cons_of_mem _ member)

/-- Actual source metadata bounds a nonempty reference fold above every earlier source effect. -/
theorem source_reference_fold_above {f : Clif.Function} {original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial)) {producer terminal : Nat}
    (producerSource : some producer ∈ sourceColorEvents original ranges)
    (terminalSource : some terminal ∈ sourceColorEvents original ranges)
    (before : producer < terminal) (indices : List Nat)
    (earlier : ∀ inst ∈ indices,producer < inst) :
    (sourceMetadata original ranges).entryColor[producer]! <
      (terminal::indices).foldl (referenceCut (sourceMetadata original ranges).entryColor) 0 := by
  have positive := source_color_positive original ranges producer producerSource
  have start := source_slot_colors_order built producer terminal producerSource terminalSource before
  have terminalPositive := source_color_positive original ranges terminal terminalSource
  simp only [List.foldl_cons,referenceCut,terminalPositive,ite_false]
  exact referenceCut_fold_above (source_metadata_positive_order built) positive rfl start indices earlier

/-- Original contiguous block slots give the actual scan its strict reverse instruction order. -/
theorem stock_lower_event_indices_reverse {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    event.indices.Pairwise (fun first second => second < first) := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,indicesEq,terminalSource,notSunk,entryColors,metadata⟩ :=
    stock_lower_event_cut_source run scope events
  rw [indicesEq]
  apply List.pairwise_cons.mpr
  constructor
  · intro inst member
    have bounds := scan_indices_bounds (blockStart f bi) block.body.length inst member
    rw [termEq]
    exact bounds.2
  · exact scan_indices_reverse_order (blockStart f bi) block.body.length

end Backend.Stock.Proof.Acquire810
