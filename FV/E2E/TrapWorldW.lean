import FV.E2E.IselSimINT
import FV.E2E.BackendWorldCleanupI
import FV.E2E.GotFlowI
import FV.E2E.PrepareSoundW

/-!
# The VCode passes keep the trap's world (SEM1 #537, traps under the oracle)

`prep_soundW`, `prune_correctW` (via `traps_cleanW`), `vTrapFrom_gotVI`, `vTrapFrom_gotV_valueI`
carry a VCode trap to the next stage with the same world at the trapping instruction (same
proofs). For `VTrapFromW` (`IselSimINT`): `prep_soundWT`, `traps_cleanWT`, `prune_correctWT`,
`vTrapFromW_gotVI`, `vTrapFromW_gotV_valueI`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof E2E

/-- **`prep_soundW`'s trap clause keeps the trap's world.** -/
theorem prep_soundWT {W : Type} {vc vcp : VCode} {sem : ISem CV W} (hds : DriverSemG sem)
    (h : prepCheck vc vcp = true) (ρ₀ : Nat → CV) (w₀ : W) (P : W → Prop) :
    ∀ c, VTrapFromW vc sem ⟨0, 0, ρ₀, w₀⟩ c P → VTrapFromW vcp sem ⟨0, 0, ρ₀, w₀⟩ c P := by
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
    intro c ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc, hP⟩
    obtain ⟨b', hLb, hb', hstar'⟩ := prep_starW hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
      ⟨b, k, ρ, w⟩ 0 rfl rfl hL0 h0
    obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i', hi', hsame⟩ := hins k i hi
    obtain ⟨hops', htc', hsem', -⟩ := sameInst_factsW hds hsame
    exact ⟨b', k, ρ, w, vb', i', ops, outs, w', hstar', hvb', hi', by rw [hops', hops],
      by rw [hsem']; exact hsem, by rw [htc']; exact htc, hP⟩
  · cases h

end Backend.Proof.Driver

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {W : Type}

private theorem entry_existsWT {vc : VCode} {sem : ISem CV W}
    {a : Nat → CV} {w : W} {b k : Nat} {a1 : Nat → CV} {w1 : W} {vb : VBlock}
    (hs : Star (VStep vc sem) (.run ⟨0, 0, a, w⟩) (.run ⟨b, k, a1, w1⟩))
    (hb : vc.blocks[b]? = some vb) : ∃ vb0, vc.blocks[0]? = some vb0 := by
  cases hs with
  | refl => exact ⟨vb, hb⟩
  | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩

/-- **`traps_cleanW` keeps the trap's world.** -/
theorem traps_cleanWT {vc : VCode} {sem : ISem CV W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {a : Nat → CV} {w0 : W} {code : Clif.TrapCode} {P : W → Prop}
    (h : VTrapFromW vc sem ⟨0, 0, a, w0⟩ code P) :
    VTrapFromW (clean vc) sem ⟨0, 0, a, w0⟩ code P := by
  obtain ⟨b, k, a1, w1, vb, i, ops, outs, w', hstar, hb, hi, hop, hs, hc, hP⟩ := h
  have hkeep : pureForm i = false := by
    cases he : pureForm i
    · rfl
    · have hn := (hp _ _ _ _ _ _ he hs).2
      cases hn
  have hkeepc : cmpForm i = false := by
    cases he : cmpForm i
    · rfl
    · have hn := (hcmp.1 _ _ _ _ _ _ he hs).1
      cases hn
  have hkeepj : isJump i = false := by
    cases he : isJump i
    · rfl
    · obtain ⟨l, rfl⟩ : ∃ l, i = .jump l := by cases i <;> simp at he; exact ⟨_, rfl⟩
      obtain ⟨-, j, hj⟩ := hcmp.2 _ _ _ _ _ _ hs
      cases hj
  obtain ⟨vb0, hb0⟩ := entry_existsWT hstar hb
  obtain ⟨c1, hstar', hr⟩ := star_sim hp hcmp ht (rel_entry hb0 a w0) hstar
  obtain ⟨k', a', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop hkeep hkeepc hkeepj
  refine ⟨b, k', a', w1, cleanBlock vc 0 vb, i, ops, outs, w', hstar', hb', hi', hop, ?_, hc, hP⟩
  rw [← hu]
  exact hs

/-- **`prune_correctW`'s trap clause keeps the trap's world.** -/
theorem prune_correctWT {vc : VCode} {sem : ISem CV W}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : CmpOverwrite sem) (ρ₀ : Nat → CV) (w₀ : W) (P : W → Prop) :
    ∀ c, VTrapFromW vc sem ⟨0, 0, ρ₀, w₀⟩ c P → VTrapFromW (prune vc) sem ⟨0, 0, ρ₀, w₀⟩ c P := by
  unfold prune
  cases h : vc.cfg with
  | error e => exact fun _ h => h
  | ok p => exact fun _ h' => traps_cleanWT hp hcmp (terminated_of_cfg h) h'

end

section
variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {XI : ExtSemI}

/-- **`vTrapFrom_gotVI` keeps the trap's world.** -/
theorem vTrapFromW_gotVI {ρ₀ : Nat → CV} {w₀ : Arm.ArmState × Nat} {c : Clif.TrapCode}
    {P : Arm.ArmState × Nat → Prop}
    (h : VTrapFromW vc (csemI F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c P) :
    VTrapFromW vc (csemVI (GotV vc) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c P := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc, hP⟩ := h
  obtain ⟨hs', -⟩ := gotInvI_star
    (show GotInvI vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc, hP⟩
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => csem F ctx (XI.at n)) hsem
  obtain ⟨-, hform⟩ := csem_halt hs1
  have hnc : ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) →
      gotGuard (GotV vc) (XI.at w.2) info (vuses ops ρ) := by
    intro info h
    exfalso
    rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> rcases h with e' | ⟨_, e'⟩ <;>
      rw [e] at e' <;> cases e'
  have hv : csemV (GotV vc) F ctx (XI.at w.2) i (vuses ops ρ) w.1 = some (outs, w'.1, .halt) := by
    rw [csemV_eq hnc]
    exact hs1
  simp only [csemVI, ISem.counted, hv, Option.map_some]
  rw [← hs2]

/-- **`vTrapFrom_gotV_valueI` keeps the trap's world.** -/
theorem vTrapFromW_gotV_valueI {ρ₀ : Nat → CV} {w₀ : Arm.ArmState × Nat} {c : Clif.TrapCode}
    {P : Arm.ArmState × Nat → Prop}
    (h : VTrapFromW vc (valueSemI F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c P) :
    VTrapFromW vc (valueSemVI (GotV vc) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ c P := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc, hP⟩ := h
  obtain ⟨hs', -⟩ := gotInvI_star_value
    (show GotInvI vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc, hP⟩
  obtain ⟨hs1, hs2⟩ := ISem.counted_some (sem := fun n => valueSem F ctx (XI.at n)) hsem
  have hp : specForm i = false := by
    cases he : specForm i
    · rfl
    · have hs : mspec ctx.slotBase i (vuses ops ρ) w.1 = some (outs, w'.1, .halt) := by
        simpa [valueSem, he] using hs1
      have hn := mspec_spec_next he hs
      cases hn
  have hsem0 : csem F ctx (XI.at w.2) i (vuses ops ρ) w.1 = some (outs, w'.1, .halt) := by
    simpa [valueSem, hp] using hs1
  obtain ⟨-, hform⟩ := csem_halt hsem0
  have hv : valueSemV (GotV vc) F ctx (XI.at w.2) i (vuses ops ρ) w.1 =
      some (outs, w'.1, .halt) := by
    simp only [valueSemV, hp, Bool.false_eq_true, ↓reduceIte]
    rw [csemV_eq fun info h => by
      rcases h with rfl | ⟨_, rfl⟩ <;> rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> cases e]
    exact hsem0
  simp only [valueSemVI, ISem.counted, hv, Option.map_some]
  rw [← hs2]

end

end E2E
