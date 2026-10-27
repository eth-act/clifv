import FVTest.E2E.FloatChecksT2
import FV.E2E.LinkScopeCtlT2

/-!
# Witnesses: the control-form checks on `fnScopeInTB2` (S11 #35)

`fW` (a float function of `fnScopeInTB2`) lowers and prepares (`FloatChecksT2.fW_pipeline`);
`ctlSpillB_of_T2` and `ctlInstsB_of_T2` then give its `ctlSpillB` and `ctlInstsB` without
running them.
-/

namespace FloatCtlT2

open Backend Backend.Proof E2E.LinkCheck FloatFinalT FloatScopeT2 FloatChecksT2

theorem fW_ctl : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    Spill.ctlSpillB vc = true ∧ ctlInstsB vcp = true := by
  obtain ⟨vc, vcp, hl, hp⟩ := fW_pipeline
  exact ⟨vc, vcp, hl, hp, ctlSpillB_of_T2 fnScopeInTB2_w hl, ctlInstsB_of_T2 fnScopeInTB2_w hl hp⟩

end FloatCtlT2
