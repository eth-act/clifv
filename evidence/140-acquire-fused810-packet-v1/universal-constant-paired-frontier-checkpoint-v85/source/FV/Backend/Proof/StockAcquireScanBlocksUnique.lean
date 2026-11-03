import FV.Backend.Proof.StockAcquireScanBlockProjection

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private def nodeOriginals : Node → List Nat
  | .original bi => [bi]
  | .edge .. => []

private theorem array_range_values {α : Type} [Inhabited α] (values : Array α) :
    (List.range values.size).map (fun index => values[index]!) = values.toList := by
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  have inside : index < values.size := by simpa using rightBound
  simp only [List.getElem_map,List.getElem_range,Array.getElem_toList,_root_.getElem!_pos values index inside]

private theorem nodeOriginals_filter (nodes : List Node) :
    nodes.flatMap nodeOriginals = nodes.filterMap (fun node => match node with | .original bi => some bi | .edge .. => none) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => cases node <;> simp [nodeOriginals,ih]

private theorem nodeOriginals_reverse (nodes : List Node) :
    nodes.reverse.flatMap nodeOriginals = (nodes.flatMap nodeOriginals).reverse := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => cases node <;> simp [List.reverse_cons,List.flatMap_append,nodeOriginals,ih]

/-- The real backward node list projects exactly to the reversed original-block list. -/
theorem backward_scan_block_projection (order : Order) :
    ((Array.range order.nodes.size).reverse.toList).flatMap
      (fun label => match order.nodes[label]! with | .original bi => [bi] | .edge .. => []) =
      (stockOriginals order.nodes).reverse := by
  have values := array_range_values order.nodes
  simp only [Array.toList_reverse,Array.toList_range]
  change (List.range order.nodes.size).reverse.flatMap (fun label => nodeOriginals order.nodes[label]!) = _
  calc
    _ = ((List.range order.nodes.size).reverse.map (fun label => order.nodes[label]!)).flatMap nodeOriginals := by
      rw [List.flatMap_map]
    _ = order.nodes.toList.reverse.flatMap nodeOriginals := by rw [List.map_reverse,values]
    _ = (stockOriginals order.nodes).reverse := by rw [nodeOriginals_reverse,nodeOriginals_filter];rfl

/-- Actual lowering records each original block exactly once in the real backward traversal. -/
theorem stock_lower_scan_block_projection {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    result.blockScans.toList.map (·.block) = (stockOriginals result.order.nodes).reverse ∧
      (result.blockScans.toList.map (·.block)).Nodup := by
  have actualRun := run
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have projection := lowerNodes_scan_block_projection hdriver
  simp only [Array.toList_empty,List.map_nil,List.nil_append] at projection
  have projection := projection.trans (backward_scan_block_projection order)
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have unique := (stock_blockOrder_originals_nodup horder nonempty).1
  refine ⟨projection,?_⟩
  rw [projection]
  apply List.pairwise_reverse.mpr
  exact unique.imp (fun different same => different same.symm)

end Backend.Stock.Proof.Acquire810
