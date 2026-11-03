import FV.Backend.Proof.StockAcquireMetadataEvents

namespace Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Every source event advances the metadata counter once. -/
theorem color_events_count (events : List (Option Nat)) (state : FenceColors.Colors) :
    (events.foldl colorEventNext state).2 = state.2 + events.length := by
  induction events generalizing state with
  | nil => simp
  | cons event events ih =>
    rw [List.foldl_cons,ih]
    cases event <;> simp [colorEventNext] <;> omega

/-- Source event writes preserve the extent of the real metadata array. -/
theorem color_events_size (events : List (Option Nat)) (state : FenceColors.Colors) :
    (events.foldl colorEventNext state).1.size = state.1.size := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    rw [List.foldl_cons,ih]
    cases event <;> simp [colorEventNext]

/-- Later events at other source slots cannot replace this source identity. -/
theorem color_events_keeps_slot (events : List (Option Nat)) (state : FenceColors.Colors)
    (target : Nat) (outside : some target ∉ events) :
    (events.foldl colorEventNext state).1[target]! = state.1[target]! := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    have tail : some target ∉ events := fun member => outside (List.mem_cons_of_mem _ member)
    rw [List.foldl_cons,ih _ tail]
    cases event with
    | none => rfl
    | some slot =>
      have different : slot ≠ target := by
        intro same
        subst slot
        exact outside (List.mem_cons_self ..)
      exact Array.getElem!_set!_ne _ _ _ _ different

/-- The source slot stores the position of its actual event, including block boundaries. -/
theorem color_event_exact (pre post : List (Option Nat)) (state : FenceColors.Colors)
    (target : Nat) (inside : target < state.1.size) (outside : some target ∉ post) :
    ((pre++some target::post).foldl colorEventNext state).1[target]! = state.2 + pre.length := by
  rw [List.foldl_append,List.foldl_cons]
  let before := pre.foldl colorEventNext state
  have size : before.1.size = state.1.size := color_events_size pre state
  have bounded : target < before.1.size := by rwa [size]
  rw [color_events_keeps_slot post (colorEventNext before (some target)) target outside]
  change (before.1.set! target before.2)[target]! = _
  have written : (before.1.set! target before.2)[target]! = before.2 := by
    simp [Array.set!_eq_setIfInBounds,bounded]
  exact written.trans (color_events_count pre state)

/-- Source event positions determine strict metadata order across the whole function. -/
theorem color_event_pair_order (pre mid post : List (Option Nat)) (state : FenceColors.Colors)
    (first second : Nat) (firstInside : first < state.1.size) (secondInside : second < state.1.size)
    (firstOutside : some first ∉ mid++some second::post) (secondOutside : some second ∉ post) :
    let final := (pre++some first::(mid++some second::post)).foldl colorEventNext state
    final.1[first]! < final.1[second]! := by
  have a := color_event_exact pre (mid++some second::post) state first firstInside firstOutside
  have b := color_event_exact (pre++some first::mid) post state second secondInside secondOutside
  have same : (pre++some first::mid)++some second::post =
      pre++some first::(mid++some second::post) := by simp only [List.append_assoc,List.cons_append]
  rw [same] at b
  change _ < _
  rw [a,b]
  simp only [List.length_append,List.length_cons] 
  omega

end Backend.Stock.Proof.Acquire810
