import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof

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

end Backend.Stock.Proof
