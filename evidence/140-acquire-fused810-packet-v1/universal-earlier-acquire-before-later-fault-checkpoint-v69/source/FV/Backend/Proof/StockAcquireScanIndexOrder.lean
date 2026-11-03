import FV.Backend.Proof.StockAcquireReferenceCutOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual reverse ranges place the source terminator first and retain every body slot. -/
theorem scan_indices_head (start count : Nat) :
    ((Array.range (count+1)).map (start+·)).reverse.toList =
      (start+count)::((Array.range count).map (start+·)).reverse.toList := by
  simp only [Array.toList_reverse,Array.toList_map,Array.toList_range,List.range_succ,
    List.map_append,List.map_cons,List.map_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.cons_append]

/-- Every actual scan index lies inside its original contiguous source range. -/
theorem scan_indices_bounds (start count inst : Nat)
    (member : inst ∈ ((Array.range count).map (start+·)).reverse.toList) :
    start ≤ inst ∧ inst < start+count := by
  simp only [Array.toList_reverse,Array.toList_map,Array.toList_range,List.mem_reverse,List.mem_map] at member
  obtain ⟨offset,inside,rfl⟩ := member
  have smaller := List.mem_range.mp inside
  omega

/-- Actual scan indices have strict reverse original source-slot order. -/
theorem scan_indices_reverse_order (start count : Nat) :
    (((Array.range count).map (start+·)).reverse.toList).Pairwise (fun first second => second < first) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [scan_indices_head,List.pairwise_cons]
    refine ⟨?_,ih⟩
    intro inst member
    exact (scan_indices_bounds start count inst member).2

end Backend.Stock.Proof.Acquire810
