import FV.Backend.Proof.StockFenceMetadataModel
import FV.Backend.Proof.StockSinkProvenance

namespace Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Every real metadata step increases its color exactly at an ordering effect. -/
theorem body_color_count (start : Nat) (xs : List (Clif.Stmt × Nat))
    (state : FenceColors.Colors) :
    (xs.foldl (FenceColors.bodyNext start) state).2 =
      state.2 + (xs.filter (fun x => colored x.1.inst)).length := by
  induction xs generalizing state with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    by_cases effect : colored x.1.inst = true
    · simp [FenceColors.bodyNext,effect,List.filter_cons]; omega
    · have quiet : colored x.1.inst = false := Bool.eq_false_iff.mpr effect
      simp [FenceColors.bodyNext,quiet,List.filter_cons]

/-- An unchanged real metadata color excludes every intervening ordering effect.
The selected root must derive this equality internally from its retained records. -/
theorem body_unchanged_color_quiet (start : Nat) (xs : List (Clif.Stmt × Nat))
    (state : FenceColors.Colors)
    (unchanged : (xs.foldl (FenceColors.bodyNext start) state).2 = state.2) :
    ∀ x ∈ xs,colored x.1.inst = false := by
  have counted := body_color_count start xs state
  have empty : (xs.filter (fun x => colored x.1.inst)).length = 0 := by omega
  intro x member
  by_cases effect : colored x.1.inst = true
  · have inside : x ∈ xs.filter (fun x => colored x.1.inst) := List.mem_filter.mpr ⟨member,effect⟩
    have absent := List.length_eq_zero_iff.mp empty
    rw [absent] at inside
    cases inside
  · exact Bool.eq_false_iff.mpr effect

end Backend.Stock.Proof.Acquire810
