import FV.E2E.UnwindStatement
import FV.E2E.Main

/-!
# `prepare` with unwinding (S10e, #232)

`prepareCorrectU_of_check`: the `prepare` validator's simulation (`prep_star`, generic in the
semantics) also carries the exceptional ends: a run of `vc` ending at a raising `call` is a run
of `vcp` ending at the same call (a `call` is not a branch: `prepare` keeps it unchanged).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof E2E

theorem setTargets_call (info : CallInfo) (ls : List Label) (i' : MInst) :
    (MInst.call info).setTargets ls ≠ some i' := by
  simp [MInst.setTargets]

/-- **`prepare` keeps the exceptional ends**: a VCode run of `vc` from the entry that ends at a
raising call is one of `vcp`. -/
theorem prep_sound_unw {vc vcp : VCode} {sem : Sem} (hds : DriverSem sem)
    (h : prepCheck vc vcp = true) (XR : XRaise) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState)
    (obj : BitVec 64) (w : Arm.ArmState) :
    VUnwFrom vc sem XR ⟨0, 0, ρ₀, w₀⟩ obj w → VUnwFrom vcp sem XR ⟨0, 0, ρ₀, w₀⟩ obj w := by
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
    intro ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem⟩
    obtain ⟨b', hLb, hb', hstar'⟩ := prep_star hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
      ⟨b, k, ρ, w1⟩ 0 rfl rfl hL0 h0
    obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i', hi', hsame⟩ := hins k _ hi
    have hi'' : i' = .call info := by
      rcases hsame with rfl | hst
      · rfl
      · exact absurd hst (setTargets_call info _ i')
    subst hi''
    exact ⟨b', k, ρ, w1, vb', info, ops, outs, hstar', hvb', hi', hops, hraise, hsem⟩
  · cases h

/-- **`prepare` preserves returns, traps and exceptional ends**, from the `prepare`
validator. -/
theorem prepareCorrectU_of_check {sem : Sem} {vc vcp : VCode} (hds : DriverSem sem)
    (h : prepCheck vc vcp = true) (XR : XRaise) : PrepareCorrectU sem XR vc vcp :=
  ⟨prepareCorrect_of_check hds h, fun ρ₀ w₀ obj w hv => prep_sound_unw hds h XR ρ₀ w₀ obj w hv⟩

end Backend.Proof.Driver
