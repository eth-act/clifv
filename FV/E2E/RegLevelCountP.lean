import FV.E2E.RegLevelCountI

/-!
# The counted run with a per-index precondition (SEM1 #537, step 2k)

`RealizesC` (`RegLevelCountI.lean`) with a precondition `P` on the segment's first state:
`RealizesCP`. The call contract of index `n` is needed only at the states of the activation's own
run whose call count is `n` (docs/plans/uninit.md §5.5); `RealizesCP.countedRun` lifts
`RealizesCP` at every index `n` with `P n` "the run's state with count `n`" to the machine with
the count (`stepC`), which stays on the run from `s0`.

* `countIn_add`, `countIn_zero_of` (no `C` state: `0`), `countIn_one_of` (exactly one: `1`);
* `RealizesCP`, `RealizesC.toCP`, `RealizesCP.countedRun`.
-/

namespace Backend.Proof

open Backend E2E

section
variable {S : Type}

theorem countIn_add (C : S → Prop) (step : S → S) (s : S) (a b : Nat) :
    countIn C step s (a + b) = countIn C step s a + countIn C step (iterN step a s) b := by
  have h := iterN_stepC C step (a + b) s 0
  rw [iterN_add, iterN_stepC, iterN_stepC] at h
  simp only [Prod.mk.injEq] at h
  omega

/-- **No `C` state among the first `n`: count `0`.** -/
theorem countIn_zero_of {C : S → Prop} {step : S → S} {s : S} :
    ∀ {n : Nat}, (∀ i < n, ¬ C (iterN step i s)) → countIn C step s n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show countIn C step s n + ind (C (iterN step n s)) = 0
    rw [countIn_zero_of fun i hi => h i (by omega)]
    simp [ind, h n (by omega)]

/-- **Exactly one `C` state among the first `n`: count `1`.** -/
theorem countIn_one_of {C : S → Prop} {step : S → S} {s : S} {i0 : Nat} :
    ∀ {n : Nat}, i0 < n → C (iterN step i0 s) → (∀ i < n, i ≠ i0 → ¬ C (iterN step i s)) →
      countIn C step s n = 1
  | 0, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hc, hn => by
    show countIn C step s n + ind (C (iterN step n s)) = 1
    rcases Nat.lt_or_ge i0 n with hlt | hge
    · rw [countIn_one_of hlt hc fun i hi => hn i (by omega)]
      simp [ind, hn n (by omega) (by omega)]
    · obtain rfl : i0 = n := by omega
      rw [countIn_zero_of fun i hi => hn i (by omega) (by omega)]
      simp [ind, hc]

end

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **`RealizesC` from the states satisfying `P`.** -/
def RealizesCP {S : Type} (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V)
    (step : S → S) (Q : S → MConf V W → Prop) (T : S → Prop) (C : S → Prop) (P : S → Prop) :
    Prop :=
  ∀ s c c', Q s c → P s → MStep vc sem keep rf c c' →
    ∃ n c'', MStep vc sem keep rf c c'' ∧ Q (iterN step n s) c'' ∧ (∀ i < n, T (iterN step i s)) ∧
      countIn C step s n = opCalls vc c

theorem RealizesC.toCP {S : Type} {sem : ISem V W} {step : S → S}
    {Q : S → MConf V W → Prop} {T C : S → Prop} (h : RealizesC vc rf sem keep step Q T C)
    (P : S → Prop) : RealizesCP vc rf sem keep step Q T C P :=
  fun s c c' hq _ hs => h s c c' hq hs

/-- **The counted semantics on the run from `s0`, the counter equal to the count**: from
`RealizesCP` at every index `n` with the precondition `P n`, where `P n` holds at the run's
states whose count is `n`, the machine with the count realises the counted semantics under `Q`
of the first components, *counter = count* and *on the run from `(s0, 0)`*. -/
theorem RealizesCP.countedRun {S : Type} {sem : Nat → ISem V W} {step : S → S}
    {Q : S → MConf V W → Prop} {T C : S → Prop} {P : Nat → S → Prop} {s0 : S}
    (h : ∀ n, RealizesCP vc rf (sem n) keep step Q T C (P n))
    (hP : ∀ i, P (countIn C step s0 i) (iterN step i s0)) :
    Realizes vc rf (ISem.counted sem) keep (stepC C step)
      (fun p c => Q p.1 (c.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
        ∃ i, p = iterN (stepC C step) i (s0, 0))
      (fun p => T p.1) := by
  rintro ⟨s, k⟩ c c' ⟨hq, hk, i, hi⟩ hs
  rw [iterN_stepC] at hi
  simp only [Prod.mk.injEq, Nat.zero_add] at hi
  obtain ⟨rfl, rfl⟩ := hi
  cases c with
  | run vs =>
    obtain ⟨b, its, m, ⟨w, n⟩⟩ := vs
    simp only [MConf.world] at hk
    subst hk
    obtain ⟨j, d, hd, hq', ht, hcnt⟩ := h _ _ _ _ hq (hP i) (MStep.counted_proj hs)
    obtain ⟨c'', rfl, hc''⟩ := MStep.counted_lift hd
    refine ⟨j, c'', hc'', ⟨?_, ?_, i + j, ?_⟩, fun i' hi' => ?_⟩
    · rw [iterN_stepC]; exact hq'
    · rw [iterN_stepC, MStep.counted_ctr hc'', hcnt, opCalls_mapW]
      rfl
    · simp only [iterN_add, iterN_stepC, Nat.zero_add]
    · rw [iterN_stepC]; exact ht i' hi'
  | ret => cases hs
  | halt => cases hs

end

end Backend.Proof
