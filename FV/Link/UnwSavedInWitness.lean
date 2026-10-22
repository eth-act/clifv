import FV.Link.UnwSavedIn
import FV.Link.UnwFnsCompleteWitness

/-!
# Witness: `savedCheck` and `unwindRows` from the frame conditions (S10g, #404)

On `E2E.DeadCleanupUnwindWitness`'s `try_call` function `tc` (spill allocation `rf`): the
decidable premises hold (`native_decide`), so `savedCheckRF_spill`, `savedCheck_of` and
`unwindRows_complete_frame` apply.
-/

namespace Link.EhCheck.Complete.Witness

open Backend Backend.Proof E2E E2E.DeadCleanupUnwindWitness

/-- The premises, decided. -/
def framePremises : Bool :=
  vcp.cfg.toBool && ctlCheck vcp rf && saveFrameB vcp rf && leadOkB rf af &&
    (vcp.blocks.size != 0) && decide (4 * fb.words.size < 2 ^ 32)

set_option maxRecDepth 100000 in
theorem framePremises_true : framePremises = true := by native_decide

theorem frame_facts :
    (∃ ss ps, vcp.cfg = .ok (ss, ps)) ∧ ctlCheck vcp rf = true ∧ saveFrameB vcp rf = true ∧
      leadOkB rf af = true ∧ vcp.blocks.size ≠ 0 ∧ 4 * fb.words.size < 2 ^ 32 := by
  have h := framePremises_true
  simp only [framePremises, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨?_, h2, h3, h4, h5, h6⟩
  cases hc : vcp.cfg with
  | error _ => rw [hc] at h1; cases h1
  | ok p => exact ⟨p.1, p.2, rfl⟩

theorem savedCheckRF_applies : savedCheckRF vcp rf = true := by
  obtain ⟨⟨ss, ps, hc⟩, hctl, -⟩ := frame_facts
  exact savedCheckRF_spill hc hctl

/-- **`savedCheck_of` applies** to `tc`. -/
theorem savedCheck_applies : savedCheck vcp rf = true :=
  savedCheck_of savedCheckRF_applies compiled.1 (Spill.spillAlloc_size vcp) frame_facts.2.2.2.2.1
    frame_facts.2.2.1 frame_facts.2.2.2.1

/-- **`unwindRows_complete_frame` applies** to `tc`. -/
theorem unwindRows_frame_applies : ∃ rows, unwindRows af fa = .ok rows :=
  unwindRows_complete_frame savedCheckRF_applies compiled.1 (Spill.spillAlloc_size vcp)
    frame_facts.2.2.2.2.1 frame_facts.2.2.1 frame_facts.2.2.2.1 compiled.2.1 compiled.2.2
    frame_facts.2.2.2.2.2

end Link.EhCheck.Complete.Witness
