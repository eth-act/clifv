module

public import FV.Backend.Proof.LowerSimMemTrap
public import FV.Backend.Proof.PrepareSound
public import FV.Backend.Proof.DeadCleanupPrepare

@[expose] public section

/-!
# A memory trap of the VCode run survives the cleanup and `prepare` (A3, #412, slice F4)

`docs/plans/memfault.md`, "Backend layers". The VCode observable of a memory trap
(`VMemTrapFrom`: the run reaches an LL/SC loop with the trap code, its address use satisfying
`A`) is kept by the passes between the lowering and the allocation, as the explicit traps are
(`traps_clean`, `prep_sound`):

* `memTraps_clean`, `memTraps_prune`: the dead-code cleanup (a loop is not a pure form, so it is
  kept, with the same use values);
* `memTraps_prep`: `prepare`, from its validator (a kept instruction is the same, or retargeted:
  a branch, never a loop).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The VCode run from the entry reaches an LL/SC loop with trap code `c` whose address use and
access size satisfy `A`. -/
def VMemTraps (vc : VCode) (sem : Sem) (ρ₀ : Nat → CV) (w₀ : Arm.ArmState) (c : Clif.TrapCode)
    (A : BitVec 64 → Nat → Prop) : Prop :=
  VMemTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c A

theorem pureForm_of_loopTrap {i : MInst} {t : Clif.TrapCode × Nat} (h : loopTrap? i = some t) :
    DeadCleanup.pureForm i = false := by
  cases i <;> simp_all [loopTrap?, DeadCleanup.pureForm]

theorem cmpForm_of_loopTrap {i : MInst} {t : Clif.TrapCode × Nat} (h : loopTrap? i = some t) :
    DeadCleanup.cmpForm i = false := by
  cases i <;> simp_all [loopTrap?, DeadCleanup.cmpForm]

theorem isJump_of_loopTrap {i : MInst} {t : Clif.TrapCode × Nat} (h : loopTrap? i = some t) :
    DeadCleanup.isJump i = false := by
  cases i <;> simp_all [loopTrap?]

theorem loopTrap?_setTargets {i i' : MInst} {ls : List Label} (h : i.setTargets ls = some i') :
    loopTrap? i' = loopTrap? i := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals first
    | (cases h; done)
    | (cases h; rfl)

theorem entry_block {V W : Type} {vc : VCode} {sem : ISem V W}
    {a : Nat → V} {w : W} {b k : Nat} {a1 : Nat → V} {w1 : W} {vb : VBlock}
    (hs : Star (VStep vc sem) (.run ⟨0, 0, a, w⟩) (.run ⟨b, k, a1, w1⟩))
    (hb : vc.blocks[b]? = some vb) : ∃ vb0, vc.blocks[0]? = some vb0 := by
  cases hs with
  | refl => exact ⟨vb, hb⟩
  | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩

/-- **The cleanup keeps a memory trap.** -/
theorem memTraps_clean {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, DeadCleanup.pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : DeadCleanup.CmpOverwrite sem)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {a : Nat → CV} {w0 : Arm.ArmState} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (h : VMemTraps vc sem a w0 c A) : VMemTraps (DeadCleanup.clean vc) sem a w0 c A := by
  obtain ⟨b, k, a1, w1, vb, i, ops, u, us, n, hstar, hb, hi, hop, hu, hlt, hA⟩ := h
  obtain ⟨vb0, hb0⟩ := entry_block hstar hb
  obtain ⟨c1, hstar', hr⟩ := DeadCleanup.star_sim hp hcmp ht (DeadCleanup.rel_entry hb0 a w0) hstar
  obtain ⟨k', a', rfl, hb', hi', hus⟩ := DeadCleanup.rel_kept hr hb hi hop (pureForm_of_loopTrap hlt)
    (cmpForm_of_loopTrap hlt) (isJump_of_loopTrap hlt)
  exact ⟨b, k', a', w1, DeadCleanup.cleanBlock vc 0 vb, i, ops, u, us, n, hstar', hb', hi', hop,
    hus ▸ hu, hlt, hA⟩

/-- **The pruning keeps a memory trap** (`prune`: the cleanup when the CFG computes). -/
theorem memTraps_prune {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, DeadCleanup.pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hcmp : DeadCleanup.CmpOverwrite sem)
    {a : Nat → CV} {w0 : Arm.ArmState} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (h : VMemTraps vc sem a w0 c A) : VMemTraps (DeadCleanup.prune vc) sem a w0 c A := by
  unfold DeadCleanup.prune
  cases hc : vc.cfg with
  | error e => exact h
  | ok p => exact memTraps_clean hp hcmp (DeadCleanup.terminated_of_cfg hc) h

/-- **`prepare` keeps a memory trap**, from its validator (as `prep_sound` for the traps). -/
theorem memTraps_prep {vc vcp : VCode} {sem : Sem} (hds : DriverSem sem)
    (h : prepCheck vc vcp = true) {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {c : Clif.TrapCode}
    {A : BitVec 64 → Nat → Prop} (ht : VMemTraps vc sem ρ₀ w₀ c A) :
    VMemTraps vcp sem ρ₀ w₀ c A := by
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
    obtain ⟨b, k, ρ, w, vb, i, ops, u, us, n, hstar, hvb, hi, hops, hu, hlt, hA⟩ := ht
    obtain ⟨b', hLb, hb', hstar'⟩ := prep_star hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
      ⟨b, k, ρ, w⟩ 0 rfl rfl hL0 h0
    obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i', hi', hsame⟩ := hins k i hi
    obtain ⟨hops', -, -, -⟩ := sameInst_facts hds hsame
    have hlt' : loopTrap? i' = loopTrap? i := by
      rcases hsame with rfl | hst
      · rfl
      · exact loopTrap?_setTargets hst
    exact ⟨b', k, ρ, w, vb', i', ops, u, us, n, hstar', hvb', hi', by rw [hops', hops], hu,
      by rw [hlt']; exact hlt, hA⟩
  · cases h

end Backend.Proof.Driver
