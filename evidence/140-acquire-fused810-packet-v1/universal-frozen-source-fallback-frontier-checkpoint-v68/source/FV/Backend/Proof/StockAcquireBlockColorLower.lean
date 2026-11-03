import FV.Backend.Proof.StockAcquireBlockBoundary

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Events before the original block boundary name strictly earlier allocated source slots. -/
theorem source_block_prefix_slots {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi target : Nat} (member : some target ∈ (f.blocks.zipIdx.take bi).flatMap (blockColorEvents ranges)) :
    target < blockStart f bi := by
  obtain ⟨x,prefixMember,eventMember⟩ := List.mem_flatMap.mp member
  obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp prefixMember
  have inside := (List.getElem?_eq_some_iff.mp found).1
  simp only [List.length_take] at inside
  have before : j < bi := by omega
  have actualFound : f.blocks.zipIdx[j]? = some x := (List.getElem?_take_of_lt before).symm.trans found
  have item := (List.getElem?_eq_some_iff.mp actualFound).2
  have indexEq := congrArg Prod.snd item
  simp only [List.getElem_zipIdx,Nat.zero_add] at indexEq
  have actualMember : x ∈ f.blocks.zipIdx := List.mem_of_getElem? actualFound
  have blockAt := List.mem_zipIdx_iff_getElem?.mp actualMember
  have bounds := block_color_event_bounds built x.2 x.1 blockAt target eventMember
  have separation := block_layout_before f.blocks x.2 bi x.1 blockAt (by omega)
  simp only [blockStart_eq] at bounds ⊢
  omega

/-- A positive source slot at or after the block start lies strictly beyond its real None boundary. -/
theorem source_slot_color_above_block_boundary {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block) {target : Nat}
    (positive : (sourceMetadata ctx ranges).entryColor[target]! ≠ 0) (afterStart : blockStart f bi ≤ target) :
    sourceBlockBoundary f ranges bi < (sourceMetadata ctx ranges).entryColor[target]! := by
  have member := source_color_positive_member ctx ranges target positive
  have lookup := source_color_event_lookup built target member
  have boundary := source_block_boundary_lookup built blockAt
  by_cases greater : sourceBlockBoundary f ranges bi < (sourceMetadata ctx ranges).entryColor[target]!
  · exact greater
  have weak : (sourceMetadata ctx ranges).entryColor[target]! ≤ sourceBlockBoundary f ranges bi := by omega
  rcases Nat.eq_or_lt_of_le weak with same | earlier
  · rw [same,boundary] at lookup
    cases lookup
  · have inside : (sourceMetadata ctx ranges).entryColor[target]! <
        ((f.blocks.zipIdx.take bi).flatMap (blockColorEvents ranges)).length := earlier
    rw [source_block_event_split built blockAt,List.append_assoc,List.getElem?_append_left inside] at lookup
    have old := source_block_prefix_slots built (List.mem_of_getElem? lookup)
    omega

end Backend.Stock.Proof.Acquire810
