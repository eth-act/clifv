import FV.Backend.Proof.StockAcquireColorSegment

namespace Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual metadata traversal retains the color-array extent. -/
theorem body_color_size (start : Nat) (xs : List (Clif.Stmt × Nat)) (state : FenceColors.Colors) :
    (xs.foldl (FenceColors.bodyNext start) state).1.size = state.1.size := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    unfold FenceColors.bodyNext
    split <;> simp

/-- Actual metadata steps at other source positions retain this slot exactly. -/
theorem body_color_keeps_slot (start : Nat) (xs : List (Clif.Stmt × Nat))
    (state : FenceColors.Colors) (target : Nat)
    (outside : ∀ x ∈ xs,start+x.2 ≠ target) :
    (xs.foldl (FenceColors.bodyNext start) state).1[target]! = state.1[target]! := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,ih (FenceColors.bodyNext start state x)
      (fun y member => outside y (List.mem_cons_of_mem _ member))]
    unfold FenceColors.bodyNext
    split
    · exact Array.getElem!_set!_ne _ _ _ _ (outside x (List.mem_cons_self ..))
    · rfl

/-- A real colored source slot contains the exact number of preceding ordering effects.
Later distinct source positions do not replace its identity. -/
theorem body_colored_exact (start : Nat) (pre post : List (Clif.Stmt × Nat))
    (state : FenceColors.Colors) (stm : Clif.Stmt) (index : Nat)
    (colored : Stock.colored stm.inst = true) (inside : start+index < state.1.size)
    (outside : ∀ x ∈ post,x.2 ≠ index) :
    ((pre++(stm,index)::post).foldl (FenceColors.bodyNext start) state).1[start+index]! =
      state.2+(pre.filter (fun x => Stock.colored x.1.inst)).length := by
  rw [List.foldl_append,List.foldl_cons]
  let before := pre.foldl (FenceColors.bodyNext start) state
  have size : before.1.size = state.1.size := body_color_size start pre state
  have bounded : start+index < before.1.size := by rwa [size]
  have kept := body_color_keeps_slot start post (FenceColors.bodyNext start before (stm,index))
    (start+index) (fun x member same => outside x member (Nat.add_left_cancel same))
  have written : (FenceColors.bodyNext start before (stm,index)).1[start+index]! = before.2 := by
    simp [FenceColors.bodyNext,colored,Array.set!_eq_setIfInBounds,bounded]
  exact kept.trans (written.trans (body_color_count start pre state))

/-- Actual metadata colors strictly follow source effect order, even with many deferred reads. -/
theorem body_colored_pair_order (start : Nat) (pre mid post : List (Clif.Stmt × Nat))
    (state : FenceColors.Colors) (first second : Clif.Stmt) (i j : Nat)
    (firstColored : Stock.colored first.inst = true) (secondColored : Stock.colored second.inst = true)
    (firstInside : start+i < state.1.size) (secondInside : start+j < state.1.size)
    (firstOutside : ∀ x ∈ mid++(second,j)::post,x.2 ≠ i)
    (secondOutside : ∀ x ∈ post,x.2 ≠ j) :
    let final := (pre++(first,i)::(mid++(second,j)::post)).foldl (FenceColors.bodyNext start) state
    final.1[start+i]! < final.1[start+j]! := by
  have firstValue := body_colored_exact start pre (mid++(second,j)::post) state first i
    firstColored firstInside firstOutside
  have secondValue := body_colored_exact start (pre++(first,i)::mid) post state second j
    secondColored secondInside secondOutside
  have same : (pre++(first,i)::mid)++(second,j)::post =
      pre++(first,i)::(mid++(second,j)::post) := by simp only [List.append_assoc,List.cons_append]
  rw [same] at secondValue
  change _ < _
  rw [firstValue,secondValue]
  have prefixCount : ((pre++(first,i)::mid).filter (fun x => Stock.colored x.1.inst)).length =
      (pre.filter (fun x => Stock.colored x.1.inst)).length+1+
        (mid.filter (fun x => Stock.colored x.1.inst)).length := by
    simp [firstColored]
    omega
  rw [prefixCount]
  omega

end Backend.Stock.Proof.Acquire810
