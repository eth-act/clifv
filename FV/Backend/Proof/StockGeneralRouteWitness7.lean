import FV.Backend.Lowering.StockGeneralLoopCfg7NI
import FV.Backend.Proof.StockGeneralLoopWitness6

/-! Non-vacuity of the loop route with jump tables: on the fixed `%f` of `jumptable.clif` (a
`br_table` on an `i32` parameter), the new provider publishes the actual unsplit Stock code, route
24 selects it, every published route before it is retained, and the previous provider does not
publish that code. -/

namespace Backend.Stock.GeneralLoopCfg7.NI.RouteFixture
open Backend
set_option autoImplicit false

private abbrev function := GeneralLoopCfg6.Fixture.jumptable

private def checks : Bool :=
  lowerRoutes.length == 25 && ParameterArgsCfg.NI.lowerRoutes.length == 24 &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    (match lowerValidated function with
      | .ok vc => decide (vc = result.code)
      | .error _ => false) &&
    (match lowerWithRoutes [(function.name,24)] function with
      | .ok vc => decide (vc = result.code)
      | .error _ => false) &&
    (match ParameterArgsCfg.NI.lowerValidated function with
      | .ok vc => !decide (vc = result.code)
      | .error _ => true)

-- witness: native_decide (the fixed function's routes and lowering only)
private theorem checks_true : checks = true := by native_decide -- witness: native_decide

theorem general_route_witness : lowerRoutes.length = 25 ∧ ParameterArgsCfg.NI.lowerRoutes.length = 24 ∧
    ∃ result,Stock.lower function = .ok result ∧
      lowerValidated function = .ok result.code ∧
      lowerWithRoutes [(function.name,24)] function = .ok result.code ∧
      ParameterArgsCfg.NI.lowerValidated function ≠ .ok result.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  obtain ⟨⟨routes,previous⟩,lowered⟩ := h
  refine ⟨routes,previous,?_⟩
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    simp only [Bool.and_eq_true] at lowered
    obtain ⟨⟨published,selected⟩,different⟩ := lowered
    refine ⟨result,rfl,?_,?_,?_⟩
    · cases out : lowerValidated function with
      | error message => rw [out] at published; cases published
      | ok vc => rw [out,decide_eq_true_eq] at published; rw [published]
    · cases out : lowerWithRoutes [(function.name,24)] function with
      | error message => rw [out] at selected; cases selected
      | ok vc => rw [out,decide_eq_true_eq] at selected; rw [selected]
    · intro same
      rw [same] at different
      simp at different

end Backend.Stock.GeneralLoopCfg7.NI.RouteFixture
