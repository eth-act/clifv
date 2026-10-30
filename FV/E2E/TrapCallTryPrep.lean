import FV.Backend.Proof.PrepareSound
import FV.Backend.Proof.RegallocTac
import FV.Backend.Proof.DeadCleanupPrepare
import FV.E2E.TrapCallTryStop

/-!
# A raising `tryCall` through the cleanup and `prepare` (S9b, #375)

`unwinds_clean`/`unwinds_prune`/`prep_sound_unw` carry a VCode run ending at a raising `call`
through the shipped pipeline's `prune` and `prepare`; here the same for a run reaching a raising
`tryCall` (`VTryRaiseFrom`): a `tryCall` is never pruned (not a pure producer), and `prepare`
keeps its call and operands (it may retarget its successors, `setTargets`).
-/

namespace Backend.DeadCleanup

open Backend Backend.Proof Backend.Proof.Driver E2E

/-- **Cleaning keeps a run to a raising `tryCall`.** -/
theorem tryRaise_clean {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {XR : XRaise} {ρ₀ : Nat → CV} {w₀ : Arm.ArmState}
    (h : VTryRaiseFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩) :
    VTryRaiseFrom (clean vc) sem XR ⟨0, 0, ρ₀, w₀⟩ := by
  obtain ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hstar, hb, hi, hop, hraise⟩ := h
  obtain ⟨vb0, hb0⟩ : ∃ vb0, vc.blocks[0]? = some vb0 := by
    cases hstar with
    | refl => exact ⟨vb, hb⟩
    | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩
  obtain ⟨c1, hstar', hr⟩ := star_sim hp hcmp ht (rel_entry hb0 ρ₀ w₀) hstar
  obtain ⟨k', ρ', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop rfl rfl rfl
  exact ⟨b, k', ρ', w1, cleanBlock vc 0 vb, info, ti, ops, obj, w', hstar', hb', hi', hop,
    by rw [← hu]; exact hraise⟩

/-- **`prune` keeps a run to a raising `tryCall`.** -/
theorem tryRaise_prune {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    {XR : XRaise} {ρ₀ : Nat → CV} {w₀ : Arm.ArmState}
    (h : VTryRaiseFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩) :
    VTryRaiseFrom (prune vc) sem XR ⟨0, 0, ρ₀, w₀⟩ := by
  unfold prune
  cases hc : vc.cfg with
  | error e => exact h
  | ok p => exact tryRaise_clean hp hcmp (terminated_of_cfg hc) h

end Backend.DeadCleanup

namespace Backend.Proof.Driver

open Backend Backend.Proof E2E

/-- A retargeted `tryCall` is a `tryCall` of the same call. -/
theorem setTargets_tryCall {info : CallInfo} {ti : TryInfo} {ls : List Label} {i' : MInst}
    (h : (MInst.tryCall info ti).setTargets ls = some i') : ∃ ti', i' = .tryCall info ti' := by
  simp only [MInst.setTargets] at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- **`prepare` keeps a run to a raising `tryCall`**: a VCode run of `vc` from the entry that
reaches a raising `tryCall` is one of `vcp`. -/
theorem prep_sound_tryRaise {vc vcp : VCode} {sem : Sem} (hds : DriverSem sem)
    (h : prepCheck vc vcp = true) (XR : XRaise) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState) :
    VTryRaiseFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩ → VTryRaiseFrom vcp sem XR ⟨0, 0, ρ₀, w₀⟩ := by
  unfold prepCheck at h
  split at h
  · rename_i ss ps ss' ps' hcfg hcfg'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, hl0⟩, hall⟩, -⟩ := h
    let L : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf ss b = true
    have hchk : ∀ b, L b → ∃ b', sigmaOf vc vcp b = some b' ∧ keptOk vc vcp ss ss' b b' = true ∧
        (ss[b]?.getD #[]).all (fun s => decide (s < vc.blocks.size) && liveOf ss s) = true := by
      intro b ⟨hlt, hlb⟩
      have := all_range hall hlt
      rw [hlb] at this
      simp only [Bool.not_true, Bool.false_or] at this
      split at this
      · cases this
      · rename_i b' hσ
        simp only [Bool.and_eq_true] at this
        exact ⟨b', hσ, this.1, this.2⟩
    have hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → Kept vc vcp ss ss' b b' := by
      intro b b' hLb hσ
      obtain ⟨b'', hσ', hkept, -⟩ := hchk b hLb
      rw [hσ] at hσ'; cases hσ'
      exact keptOk_sound hkept
    have hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s := by
      intro b sb j s hLb hsb hs
      obtain ⟨-, -, -, hall'⟩ := hchk b hLb
      rw [hsb, Option.getD_some] at hall'
      have := (Array.all_eq_true_iff_forall_mem.mp hall') s (Array.mem_of_getElem? hs)
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
    have hL0 : L 0 := by
      refine ⟨?_, hl0⟩
      unfold sigmaOf at h0
      split at h0
      · rename_i vb hvb; exact (Array.getElem?_eq_some_iff.mp hvb).1
      · cases h0
    intro ⟨b, k, ρ, w1, vb, info, ti, ops, obj, w', hstar, hvb, hi, hops, hraise⟩
    obtain ⟨b', hLb, hb', hstar'⟩ := prep_star hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
      ⟨b, k, ρ, w1⟩ 0 rfl rfl hL0 h0
    obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i', hi', hsame⟩ := hins k _ hi
    obtain ⟨ti', rfl⟩ : ∃ ti', i' = .tryCall info ti' := by
      rcases hsame with rfl | hst
      · exact ⟨ti, rfl⟩
      · exact setTargets_tryCall hst
    exact ⟨b', k, ρ, w1, vb', info, ti', ops, obj, w', hstar', hvb', hi',
      by rw [operands_tryCall_call]; rw [operands_tryCall_call] at hops; exact hops, hraise⟩
  · cases h

end Backend.Proof.Driver

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The cleanup pipeline keeps a run to a raising `tryCall`** (`prune`, then `prepare`, for a
semantics with `DriverSem` whose pure producers keep the world and continue, and in which a
compare's flags are overwritten by the next compare). -/
theorem tryRaise_cleanup {sem : Sem} {vc vcp : VCode} (hds : DriverSem sem)
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (h : prepCheck (prune vc) vcp = true) (XR : XRaise) {ρ₀ : Nat → CV} {w₀ : Arm.ArmState}
    (hv : VTryRaiseFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩) : VTryRaiseFrom vcp sem XR ⟨0, 0, ρ₀, w₀⟩ :=
  prep_sound_tryRaise hds h XR ρ₀ w₀ (tryRaise_prune hp hcmp hv)

end E2E
