import FV.Backend.Lowering.StockParameterArgsCfgNI
import FV.Backend.Proof.StockParameterArgsWitness

/-! Non-vacuity of the argument-passing route: on the fixed parameter CFG with block arguments,
the new provider publishes the actual split code, route 22 selects it, every published route
before it is retained, and the previous provider publishes different code. -/

namespace Backend.Stock.ParameterArgsCfg.NI.RouteFixture
open Backend
set_option autoImplicit false

private abbrev function := ParameterArgsCfg.Fixture.function

private def checks : Bool :=
  lowerRoutes.length == 23 && VoidCall.NI.lowerRoutes.length == 22 &&
  match Stock.lower function with
  | .error _ => false
  | .ok result => match splitEdgesChecked result.code result.edgeArgs with
    | .error _ => false
    | .ok split =>
      (match lowerValidated function with
        | .ok vc => decide (vc = split.code)
        | .error _ => false) &&
      (match lowerWithRoutes [(function.name,22)] function with
        | .ok vc => decide (vc = split.code)
        | .error _ => false) &&
      (match VoidCall.NI.lowerValidated function with
        | .ok vc => !decide (vc = split.code)
        | .error _ => true)

-- witness: native_decide (the fixed function's routes, lowering and split only)
private theorem checks_true : checks = true := by native_decide

theorem argument_route_witness : lowerRoutes.length = 23 ∧ VoidCall.NI.lowerRoutes.length = 22 ∧
    ∃ result split,Stock.lower function = .ok result ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      lowerValidated function = .ok split.code ∧
      lowerWithRoutes [(function.name,22)] function = .ok split.code ∧
      VoidCall.NI.lowerValidated function ≠ .ok split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  obtain ⟨⟨routes,previous⟩,lowered⟩ := h
  refine ⟨routes,previous,?_⟩
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    dsimp only at lowered
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => rw [splitRun] at lowered; cases lowered
    | ok split =>
      rw [splitRun] at lowered
      dsimp only at lowered
      simp only [Bool.and_eq_true] at lowered
      obtain ⟨⟨published,routed⟩,differs⟩ := lowered
      refine ⟨result,split,rfl,splitRun,?_,?_,?_⟩
      · cases out : lowerValidated function with
        | error message => rw [out] at published; cases published
        | ok vc => rw [out] at published; simpa using published
      · cases out : lowerWithRoutes [(function.name,22)] function with
        | error message => rw [out] at routed; cases routed
        | ok vc => rw [out] at routed; simpa using routed
      · intro same
        rw [same] at differs
        simp at differs

end Backend.Stock.ParameterArgsCfg.NI.RouteFixture
