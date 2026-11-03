import FV.Backend.Proof.StockAcquireBlockColorLower

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual boundary-free interval cannot place the runtime color before the original block boundary. -/
theorem SourceColorGap.above_block_boundary {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block)
    {cut color : Nat} {state : State} (covered : SourceColorGap ctx ranges cut state)
    (actual : state.color = some color) (inside : sourceBlockBoundary f ranges bi < cut) :
    sourceBlockBoundary f ranges bi < color := by
  by_cases above : sourceBlockBoundary f ranges bi < color
  · exact above
  have lower : color ≤ sourceBlockBoundary f ranges bi := by omega
  obtain ⟨producer,found⟩ := covered color actual (sourceBlockBoundary f ranges bi) lower inside
  rw [source_block_boundary_lookup built blockAt] at found
  cases found

/-- Every nonempty actual block prefix keeps its source cut beyond the original boundary. -/
theorem source_reference_fold_above_block_boundary {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block)
    {terminal : Nat} (source : some terminal ∈ sourceColorEvents ctx ranges)
    (terminalInside : blockStart f bi ≤ terminal) (indices : List Nat)
    (inside : ∀ inst ∈ indices,blockStart f bi ≤ inst) :
    sourceBlockBoundary f ranges bi <
      (terminal::indices).foldl (referenceCut (sourceMetadata ctx ranges).entryColor) 0 := by
  have positive := source_color_event_nonzero built terminal source
  have start := source_slot_color_above_block_boundary built blockAt positive terminalInside
  simp only [List.foldl_cons,referenceCut,positive,ite_false]
  apply referenceCut_fold_above start indices
  intro inst member positive
  exact source_slot_color_above_block_boundary built blockAt positive (inside inst member)

/-- The original prefix indices internally place the reference cut inside the actual source block. -/
theorem stock_lower_prefix_cut_above_boundary {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices suffix : List Nat}
    (parts : event.indices = indices++suffix) (nonempty : indices ≠ []) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (bi : Nat) (block : Clif.Block),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[bi]? = some block ∧
      event.termInst = blockStart f bi+block.body.length ∧
      sourceBlockBoundary f ranges bi <
        indices.foldl (referenceCut (sourceMetadata original ranges).entryColor) 0 := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,indicesEq,terminalSource,notSunk,entryColors,metadata⟩ :=
    stock_lower_event_cut_source run scope events
  refine ⟨original,ranges,initial,bi,block,built,blockAt,termEq,?_⟩
  cases indices with
  | nil => exact False.elim (nonempty rfl)
  | cons first indices =>
    have compared := List.cons.inj (indicesEq.symm.trans parts)
    have firstEq : first = event.termInst := compared.1.symm
    subst first
    have bodyParts : ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList = indices++suffix := compared.2
    apply source_reference_fold_above_block_boundary built blockAt terminalSource (by omega) indices
    intro inst member
    have bodyMember : inst ∈ ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList := by
      rw [bodyParts]
      exact List.mem_append_left _ member
    exact (scan_indices_bounds (blockStart f bi) block.body.length inst bodyMember).1

end Backend.Stock.Proof.Acquire810
