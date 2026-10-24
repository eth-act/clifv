import FVTest.E2E.FloatTotalT
import FV.E2E.LinkScopeInputT3

/-!
# Witnesses: the decider-free typed scope `fnScopeInTB3` (S11 #35)

`FloatFinalT.fW` (float `load`, `f64const`, `select`, `store`, `bitcast`; outside subset E) and
`FloatTotalT.crateW` meet the decided input conditions `fnScopeInTB3` / `InScopeInT3`
(`native_decide`, witness only); the run-time checks, `lowerFunction`'s success and the
pipeline's totality then follow by the theorems of `FV/E2E/LinkScopeInputT3.lean`.
`lake build FVTest.E2E.FloatScopeT3`.
-/

namespace FloatScopeT3

open Backend Backend.Proof E2E E2E.LinkCheck FloatFinalT FloatLinkT FloatTotalT

theorem fnScopeInTB3_w : fnScopeInTB3 fW = true := by native_decide

theorem inScopeInT3_w : InScopeInT3 crateW = true := by native_decide

/-- **Witness**: `fW`'s run-time decider holds by the theorem. -/
theorem lowerOutTB_w : lowerOutTB fW = true := lowerOutTB_of_T3 fnScopeInTB3_w

theorem fnScopeInTB2_w3 : fnScopeInTB2 fW = true := fnScopeInTB2_of_T3 fnScopeInTB3_w

theorem lowerFunction_ok_w : ∃ vc, lowerFunction fW = .ok vc := lowerFunction_ok_T3 fnScopeInTB3_w

/-- **Witness**: the four checks and the emission conditions of `fW`'s code, by the theorems. -/
theorem checks_w : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    Spill.ctlSpillB vc = true ∧ ctlInstsB vcp = true ∧ formsCoveredB default vcp = true ∧
    emitCondsB vcp = true ∧ Spill.resClassOkB fW = true := by
  obtain ⟨vc, hl⟩ := lowerFunction_ok_w
  obtain ⟨vcp, hp⟩ := Prep.prepare_okT dominated_w lowerScopeT_w hl
  exact ⟨vc, vcp, hl, hp, ctlSpillB_of_T3 fnScopeInTB3_w hl, ctlInstsB_of_T3 fnScopeInTB3_w hl hp,
    formsCoveredB_of_T3 fnScopeInTB3_w hl hp default, emitCondsB_of_T3 fnScopeInTB3_w hl hp,
    resClassOkB_of_T3 fnScopeInTB3_w⟩

/-- **Witness**: the pipelines compile `fW` for every allocator answer. -/
theorem pipeT_okT3_w (o : Lean.Json) : ∃ a, pipeT fW 0 0 o = .ok a :=
  let ⟨a, ha, _⟩ := pipeT_okT3 fnScopeInTB3_w 0 0 o
  ⟨a, ha⟩

theorem pipeCleanupT_okT3_w (o : Lean.Json) : ∃ a, pipeCleanupT fW 0 0 o = .ok a :=
  let ⟨a, ha, _⟩ := pipeCleanupT_okT3 fnScopeInTB3_w 0 0 o
  ⟨a, ha⟩

theorem resultsCleanupT_ok_inT3_w : crateW.resultsCleanupT.all (·.2.toBool) = true :=
  resultsCleanupT_ok_inT3 inScopeInT3_w

theorem inScopePT_w : InScopePT crateW = true := inScopePT_of_inT3 inScopeInT3_w

end FloatScopeT3
