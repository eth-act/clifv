import FV.E2E.RegLevelForward2

/-!
# The joint realisation with the call count (SEM1 #537, item (3))

`RealizesCP.countedRun` for two machines realising two allocated-code runs jointly
(`RealizesJ`, `RegLevelForward2.lean`): `RealizesJCP` is the per-call-number joint realisation
from start states satisfying the preconditions `P n`, `P' n'` (the contracts of the two runs'
call numbers), counting the call states of each segment; `RealizesJCP.countedRun2` lifts it to
the two machines with their counts, on the runs from `(s0, 0)`, `(s0', 0)` at the same index.
-/

namespace Backend.Proof

open Backend E2E

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

theorem MConf.shapeEq_mapW {W' : Type} (π : W → W') {c c' : MConf V W}
    (h : MConf.ShapeEq c c') : MConf.ShapeEq (c.mapW π) (c'.mapW π) := by
  cases c with
  | run s =>
    cases c' with
    | run s' => exact h
    | ret => exact h.elim
    | halt => exact h.elim
  | ret =>
    cases c' with
    | ret => trivial
    | run => exact h.elim
    | halt => exact h.elim
  | halt =>
    cases c' with
    | halt => trivial
    | run => exact h.elim
    | ret => exact h.elim

/-- **The joint realisation from start states satisfying `P`, `P'`**, counting the `C`, `C'`
states of each segment (`opCalls` of the configurations realised). -/
def RealizesJCP {S : Type} (vc : VCode) (rf : RFunc) (sem sem' : ISem V W) (keep : Reg → V → V)
    (step step' : S → S) (K : MConf V W → MConf V W → Prop)
    (J : S → MConf V W → S → MConf V W → Prop) (T : S → S → Prop) (C C' P P' : S → Prop) :
    Prop :=
  ∀ s c s' c' d d', J s c s' c' → P s → P' s' → MStep vc sem keep rf c d →
    MStep vc sem' keep rf c' d' →
    (∀ e e', MStep vc sem keep rf c e → MStep vc sem' keep rf c' e' →
      MConf.ShapeEq e e' ∧ K e e') →
    ∃ n e e', MStep vc sem keep rf c e ∧ MStep vc sem' keep rf c' e' ∧
      J (iterN step n s) e (iterN step' n s') e' ∧
      (∀ i < n, T (iterN step i s) (iterN step' i s')) ∧
      countIn C step s n = opCalls vc c ∧ countIn C' step' s' n = opCalls vc c'

/-- **The counted joint semantics on the runs from `(s0, 0)`, `(s0', 0)`** (as
`RealizesCP.countedRun`): from `RealizesJCP` at every pair of call numbers, with the
preconditions holding at the runs' states of those counts, the two machines with their counts
realise the two counted runs jointly under `J` of the first components, *counters = counts*, at
one index of both runs. -/
theorem RealizesJCP.countedRun2 {S : Type} {sem sem' : Nat → ISem V W} {step step' : S → S}
    {K : MConf V W → MConf V W → Prop} {J : S → MConf V W → S → MConf V W → Prop}
    {T : S → S → Prop} {C C' : S → Prop} {P P' : Nat → S → Prop} {s0 s0' : S}
    (h : ∀ n n', RealizesJCP vc rf (sem n) (sem' n') keep step step' K J T C C' (P n) (P' n'))
    (hP : ∀ i, P (countIn C step s0 i) (iterN step i s0))
    (hP' : ∀ i, P' (countIn C' step' s0' i) (iterN step' i s0')) :
    RealizesJ vc rf (ISem.counted sem) (ISem.counted sem') keep (stepC C step) (stepC C' step')
      (fun e e' => K (e.mapW Prod.fst) (e'.mapW Prod.fst))
      (fun p c p' c' => J p.1 (c.mapW Prod.fst) p'.1 (c'.mapW Prod.fst) ∧ p.2 = c.world.2 ∧
        p'.2 = c'.world.2 ∧ ∃ i, p = iterN (stepC C step) i (s0, 0) ∧
          p' = iterN (stepC C' step') i (s0', 0))
      (fun p p' => T p.1 p'.1) := by
  rintro ⟨s, k⟩ c ⟨s', k'⟩ c' d d' ⟨hj, hk, hk', i, hi, hi'⟩ hd hd' hsh
  rw [iterN_stepC] at hi hi'
  simp only [Prod.mk.injEq, Nat.zero_add] at hi hi'
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨rfl, rfl⟩ := hi'
  cases c with
  | run vs =>
    obtain ⟨b, its, m, ⟨w, n⟩⟩ := vs
    simp only [MConf.world] at hk
    subst hk
    cases c' with
    | run vs' =>
      obtain ⟨b', its', m', ⟨w', n'⟩⟩ := vs'
      simp only [MConf.world] at hk'
      subst hk'
      obtain ⟨j, e, e', he, he', hj', ht, hcnt, hcnt'⟩ :=
        h _ _ _ _ _ _ _ _ hj (hP i) (hP' i) (MStep.counted_proj hd) (MStep.counted_proj hd')
          fun e e' a b' => by
            obtain ⟨f, rfl, hf⟩ := MStep.counted_lift a
            obtain ⟨f', rfl, hf'⟩ := MStep.counted_lift b'
            obtain ⟨hs, hK⟩ := hsh f f' hf hf'
            exact ⟨MConf.shapeEq_mapW Prod.fst hs, hK⟩
      obtain ⟨f, rfl, hf⟩ := MStep.counted_lift he
      obtain ⟨f', rfl, hf'⟩ := MStep.counted_lift he'
      refine ⟨j, f, f', hf, hf', ⟨?_, ?_, ?_, i + j, ?_, ?_⟩, fun i' hi' => ?_⟩
      · rw [iterN_stepC, iterN_stepC]; exact hj'
      · rw [iterN_stepC, MStep.counted_ctr hf, hcnt, opCalls_mapW]
        rfl
      · rw [iterN_stepC, MStep.counted_ctr hf', hcnt', opCalls_mapW]
        rfl
      · simp only [iterN_add, iterN_stepC, Nat.zero_add]
      · simp only [iterN_add, iterN_stepC, Nat.zero_add]
      · rw [iterN_stepC, iterN_stepC]; exact ht i' hi'
    | ret => cases hd'
    | halt => cases hd'
  | ret => cases hd
  | halt => cases hd

end

end Backend.Proof
