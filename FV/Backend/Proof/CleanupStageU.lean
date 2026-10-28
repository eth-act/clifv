import FV.Backend.Proof.LowerSimUCheck
import FV.Backend.Proof.CleanupStageFacts
import FV.Backend.Proof.LowerSimSkipU

/-!
# The skip of unused instructions under the unwinding validator

`skipStage_specU`: `skipStage_spec` together with the exceptional-edge facts (`UnwShape`) of
`loweringU_of_check`, for one renaming and lowering record, so the driver simulation with
unwinding of the kept code (`driver_correctU_stage`) applies to `skipStage f vc`.
-/

namespace Backend.Proof.Driver
open Backend Backend.Proof

/-- **The skip's hypotheses under `lowerCheckU`**: the lowering obligations of `vc` with its
`UnwShape`, and, for the same renaming and lowering record, `skipStage f vc` is `vc` or the
deletion `SkipHyp` describes it. -/
theorem skipStage_specU {f : Clif.Function} {vc : VCode} (h : lowerCheckU f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧ UnwShape f vc ctx R gn bl A ∧
      (skipStage f vc = vc ∨
        SkipHyp f vc R bl (skipAt f (skipDrops f R bl vc)) (skipStage f vc)) := by
  have hlc : lowerCheck f vc = true := by
    simp only [lowerCheckU, Bool.and_eq_true] at h
    exact h.1
  simp only [lowerCheckU, Bool.and_eq_true] at h
  obtain ⟨hc, hu⟩ := h
  unfold unwCheck at hu
  split at hu
  · cases hu
  · rename_i ctx ranges st0 hb
    split at hu
    · cases hu
    · rename_i bl hl
      unfold lowerCheck at hc
      rw [hb] at hc
      dsimp only at hc
      rw [hl] at hc
      dsimp only at hc
      simp only [Bool.and_eq_true] at hc
      have hS := lowerShape_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) hc.1.1.1.1
      have hcert := hc.1.1.1.2
      have hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB →
          bl[tl]? = some TL → DefsAt ctx TB TL.start := by
        intro tl TB TL hTB hTL
        simp only [certOk, Bool.and_eq_true] at hcert
        have := all_range hcert.1.1.2 (by simpa using lt_of_getElem? hTB)
        have hok : certBlockOk f ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl)))
            f.blocks.toArray bl.toArray (inFix f ctx (gnAt (gnTable st0.nextVreg (aliasOf f bl))))
            tl TB TL = true := by
          simpa [List.getElem?_toArray, hTB, hTL] using this
        exact (certBlockOk_spec hok).2.1
      refine ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len hcert, brIdx_of_ok hc.1.1.2,
        unwShape_of_ok hS.len hD hu, ?_⟩
      unfold skipStage
      cases hE : Compile.functionE f
      · exact .inl (by simp [hE])
      · rw [ite_cond_eq_true _ _ (by simp [hlc])]
        unfold skipDead
        rw [hb]
        simp only
        rw [hl]
        simp only
        split
        · rename_i hk
          exact .inr ⟨rfl, hk, skipOk_skipAt f _⟩
        · exact .inl rfl

end Backend.Proof.Driver
