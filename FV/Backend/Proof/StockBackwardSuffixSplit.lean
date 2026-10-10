import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver

/-- Every node already visited before the owner in the actual reverse traversal
has a larger, in-bounds label. -/
theorem stock_backward_prefix_bounds {n label : Nat} {earlier suffix : List Nat}
    (split : (Array.range n).reverse.toList = earlier ++ label :: suffix) :
    ∀ k ∈ earlier, label < k ∧ k < n := by
  simp only [Array.toList_reverse, Array.toList_range] at split
  induction n generalizing earlier with
  | zero =>
    simp only [List.range_zero, List.reverse_nil] at split
    have member : label ∈ ([] : List Nat) := by rw [split]; simp
    cases member
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append] at split
    cases earlier with
    | nil => simp
    | cons head rest =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, tail⟩ := split
      have owner : label < n := by
        have member : label ∈ (List.range n).reverse := by rw [tail]; simp
        simpa only [List.mem_reverse, List.mem_range] using member
      intro k member
      rcases List.mem_cons.mp member with same | member
      · subst k; exact ⟨owner, Nat.lt_succ_self n⟩
      · have bounds := ih tail k member
        exact ⟨bounds.1, Nat.lt_trans bounds.2 (Nat.lt_succ_self n)⟩

/-- Actual block-order uniqueness excludes the owner's source block from every
node in the already executed prefix, including orders with inserted edge nodes. -/
theorem stock_blockOrder_backward_prefix_others {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0)
    {label owner : Nat} {earlier suffix : List Nat}
    (defined : order.nodes[label]? = some (.original owner))
    (split : (Array.range order.nodes.size).reverse.toList = earlier ++ label :: suffix) :
    ∀ k ∈ earlier, ∀ bi,
      order.nodes[k]! = .original bi → bi < f.blocks.length ∧ bi ≠ owner := by
  intro k member bi node
  obtain ⟨later, inside⟩ := stock_backward_prefix_bounds split k member
  have lookup : order.nodes[k]? = some (.original bi) := by
    rw [getElem!_pos order.nodes k inside] at node
    simp only [Array.getElem?_eq_getElem inside, node]
  have projected : bi ∈ stockOriginals order.nodes := by
    unfold stockOriginals
    exact List.mem_filterMap.mpr ⟨.original bi,
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  refine ⟨(stock_blockOrder_originals_nodup run nonempty).2 bi projected, ?_⟩
  intro same
  subst bi
  have equal := stock_blockOrder_original_unique run nonempty lookup defined
  omega

/-- Splitting the driver's actual reverse index order at a processed label
identifies its remaining suffix exactly, including the label's array bound. -/
theorem stock_backward_suffix_split {n label : Nat} {earlier suffix : List Nat}
    (split : (Array.range n).reverse.toList = earlier ++ label :: suffix) :
    label < n ∧ suffix = (Array.range label).reverse.toList := by
  simp only [Array.toList_reverse, Array.toList_range] at split ⊢
  induction n generalizing earlier with
  | zero =>
    simp only [List.range_zero, List.reverse_nil] at split
    have member : label ∈ ([] : List Nat) := by rw [split]; simp
    cases member
  | succ n ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append] at split
    cases earlier with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨same, tail⟩ := split
      subst label
      exact ⟨Nat.lt_succ_self n, tail.symm⟩
    | cons k rest =>
      simp only [List.cons_append, List.cons.injEq] at split
      have result := ih split.2
      exact ⟨Nat.lt_trans result.1 (Nat.lt_succ_self n), result.2⟩

/-- A nonempty prefix and suffix in the four-node traversal instantiate the
exact decomposition used after lowering label1. -/
theorem stock_backward_suffix_split_witness :
    (Array.range 4).reverse.toList = [3, 2] ++ 1 :: [0] ∧
      1 < 4 ∧ ([0] : List Nat) = (Array.range 1).reverse.toList := by
  have split : (Array.range 4).reverse.toList = [3, 2] ++ 1 :: [0] := by
    simp only [Array.toList_reverse, Array.toList_range]
    decide
  exact ⟨split, stock_backward_suffix_split split⟩

/-- The same nonempty actual prefix inhabits the bounds result. -/
theorem stock_backward_prefix_bounds_witness :
    (Array.range 4).reverse.toList = [3, 2] ++ 1 :: [0] ∧
      (∀ k ∈ ([3, 2] : List Nat), 1 < k ∧ k < 4) := by
  have split : (Array.range 4).reverse.toList = [3, 2] ++ 1 :: [0] := by
    simp only [Array.toList_reverse, Array.toList_range]
    decide
  exact ⟨split, stock_backward_prefix_bounds split⟩

private def prefixFunction : Clif.Function := {
  name := "parallel_prefix_source_edges"
  sig := {}
  blocks := [
    { id := 7, params := [], body := [], term := .brif 0 ⟨9, []⟩ ⟨9, []⟩ },
    { id := 9, params := [], body := [], term := .ret [] }] }
private def prefixOrder : Order :=
  ⟨#[.original 0, .edge 0 0 1, .edge 0 1 1, .original 1],
    #[#[1, 2], #[3], #[3], #[]]⟩

/-- A real order with two inserted edges has an already visited prefix
containing both edges and a different source original. -/
theorem stock_blockOrder_backward_prefix_others_witness :
    blockOrder prefixFunction = .ok prefixOrder ∧
    prefixOrder.nodes[0]? = some (.original 0) ∧
    (Array.range prefixOrder.nodes.size).reverse.toList = [3, 2, 1] ++ 0 :: [] ∧
    (∀ k ∈ ([3, 2, 1] : List Nat), ∀ bi,
      prefixOrder.nodes[k]! = .original bi → bi < prefixFunction.blocks.length ∧ bi ≠ 0) := by
  have ordered : blockOrder prefixFunction = .ok prefixOrder := by cbv
  have split : (Array.range prefixOrder.nodes.size).reverse.toList = [3, 2, 1] ++ 0 :: [] := by
    simp only [Array.toList_reverse, Array.toList_range]
    decide
  exact ⟨ordered, rfl, split,
    stock_blockOrder_backward_prefix_others ordered (by decide) rfl split⟩

end Backend.Stock.Proof
