import FV.Backend.Proof.RegallocSound

/-!
# Forward simulation through the checker's relation (M6 proof)

`checkAlloc_sound` gives a relation `R` between allocated-code configurations and VCode
configurations. To prove that a *concrete* machine (the Arm model running the laid-out code)
realises every VCode run, we go forward along the VCode run: the concrete machine realises
*some* `MStep` successor of its current allocated-code configuration (`Realizes`); `R`'s step
property plus the determinism of `VStep` (`VStep_det`) put that successor on the given VCode
run, and moves (which make no VCode step) strictly decrease the item measure.

* `forward`: every VCode run `v →* v'` from related configurations is realised: some number of
  machine steps reaches a configuration related to `v'`;
* `forward_op`: at a VCode run state that can step, the machine can be advanced past the
  pending moves to the instruction item itself.
-/

namespace Backend.Proof

open Backend

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {sem : ISem V W} {keep : Reg → V → V}

/-- `n` steps of a deterministic machine. -/
def iterN (f : S → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => iterN f n (f s)

theorem iterN_add (f : S → S) (a b : Nat) (s : S) :
    iterN f (a + b) s = iterN f b (iterN f a s) := by
  induction a generalizing s with
  | zero => simp [iterN]
  | succ a ih =>
    rw [Nat.add_right_comm, iterN, iterN, ih]

theorem VNext_det {b k n : Nat} {i : MInst} {uses : List V} {ρ : Nat → V} {w : W} {ctl : Ctl}
    {c1 c2 : VConf V W} (h1 : VNext vc b k n i uses ρ w ctl c1)
    (h2 : VNext vc b k n i uses ρ w ctl c2) : c1 = c2 := by
  cases h1 with
  | next => cases h2; rfl
  | goto _ hs1 he1 =>
    cases h2 with
    | goto _ hs2 he2 =>
      rw [hs1] at hs2
      cases hs2
      rw [he1] at he2
      cases he2
      rfl
  | ret => cases h2; rfl
  | halt => cases h2; rfl

/-- `VStep` is deterministic (the instruction semantics is a function). -/
theorem VStep_det {v v1 v2 : VConf V W} (h1 : VStep vc sem v v1) (h2 : VStep vc sem v v2) :
    v1 = v2 := by
  cases h1 with
  | step hvb hi hops hsem _ hn =>
    cases h2 with
    | step hvb' hi' hops' hsem' _ hn' =>
      rw [hvb] at hvb'
      cases hvb'
      rw [hi] at hi'
      cases hi'
      rw [hops] at hops'
      cases hops'
      rw [hsem] at hsem'
      cases hsem'
      exact VNext_det hn hn'

/-- The concrete machine `step` realises the allocated code under `Q`: from a related state it
reaches (in some number of steps) a state related to some `MStep` successor, every state of the
way before it satisfying `T` (a trace invariant; `fun _ => True` for none). -/
def Realizes (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V) (step : S → S)
    (Q : S → MConf V W → Prop) (T : S → Prop) : Prop :=
  ∀ s c c', Q s c → MStep vc sem keep rf c c' →
    ∃ n c'', MStep vc sem keep rf c c'' ∧ Q (iterN step n s) c'' ∧ ∀ i < n, T (iterN step i s)

/-- Traces compose: `T` before `a` steps from `s` and before `b` steps from there. -/
theorem trace_add {step : S → S} {T : S → Prop} {s : S} {a b : Nat}
    (ha : ∀ i < a, T (iterN step i s)) (hb : ∀ i < b, T (iterN step i (iterN step a s))) :
    ∀ i < a + b, T (iterN step i s) := by
  intro i hi
  by_cases h : i < a
  · exact ha i h
  · have := hb (i - a) (by omega)
    rwa [← iterN_add, show a + (i - a) = i by omega] at this

theorem forward_aux {R : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {v v' : VConf V W} (hv : Star (VStep vc sem) v v') :
    ∀ k (c : MConf V W) s, c.measure ≤ k → R c v → Q s c →
      ∃ n c', Q (iterN step n s) c' ∧ R c' v' ∧ ∀ i < n, T (iterN step i s) := by
  induction hv with
  | refl => exact fun _ c s _ hr hq => ⟨0, c, hq, hr, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | @step v v1 v' h1 _ ih =>
    intro k
    induction k with
    | zero =>
      intro c s hk hr hq
      obtain ⟨c', hc'⟩ := hR.progress hr h1
      obtain ⟨n1, c'', hs, hq', ht1⟩ := hQ s c c' hq hc'
      rcases hR.step hr hs with ⟨_, hlt⟩ | ⟨v'', hv'', hr''⟩
      · omega
      · rw [VStep_det hv'' h1] at hr''
        obtain ⟨n2, c3, hq3, hr3, ht2⟩ := ih c''.measure c'' _ (Nat.le_refl _) hr'' hq'
        exact ⟨n1 + n2, c3, by rw [iterN_add]; exact hq3, hr3, trace_add ht1 ht2⟩
    | succ k ihk =>
      intro c s hk hr hq
      obtain ⟨c', hc'⟩ := hR.progress hr h1
      obtain ⟨n1, c'', hs, hq', ht1⟩ := hQ s c c' hq hc'
      rcases hR.step hr hs with ⟨hr'', hlt⟩ | ⟨v'', hv'', hr''⟩
      · obtain ⟨n2, c3, hq3, hr3, ht2⟩ := ihk c'' _ (by omega) hr'' hq'
        exact ⟨n1 + n2, c3, by rw [iterN_add]; exact hq3, hr3, trace_add ht1 ht2⟩
      · rw [VStep_det hv'' h1] at hr''
        obtain ⟨n2, c3, hq3, hr3, ht2⟩ := ih c''.measure c'' _ (Nat.le_refl _) hr'' hq'
        exact ⟨n1 + n2, c3, by rw [iterN_add]; exact hq3, hr3, trace_add ht1 ht2⟩

/-- **Forward simulation.** Every VCode run from a configuration related to the machine's is
realised by the machine (every state of the way satisfying the trace invariant). -/
theorem forward {R : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {v v' : VConf V W} (hv : Star (VStep vc sem) v v') {c : MConf V W} {s : S}
    (hr : R c v) (hq : Q s c) :
    ∃ n c', Q (iterN step n s) c' ∧ R c' v' ∧ ∀ i < n, T (iterN step i s) :=
  forward_aux hR hQ hv _ c s (Nat.le_refl _) hr hq

/-- At a VCode run state that can step, the machine can be advanced past the pending moves:
its next item is the instruction the VCode executes. -/
theorem forward_op {R : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {vs : VState V W} {v1 : VConf V W} (h1 : VStep vc sem (.run vs) v1) :
    ∀ k (c : MConf V W) s, c.measure ≤ k → R c (.run vs) → Q s c →
      ∃ n b a its m w, Q (iterN step n s) (.run ⟨b, .op vs.k a :: its, m, w⟩) ∧
        R (.run ⟨b, .op vs.k a :: its, m, w⟩) (.run vs) := by
  intro k
  induction k with
  | zero =>
    intro c s hk hr hq
    obtain ⟨c', hc'⟩ := hR.progress hr h1
    cases hc' with
    | move => simp [MConf.measure] at hk
    | op =>
      obtain ⟨-, hk', -⟩ := hR.at_op hr
      rw [← hk'] at hr hq
      exact ⟨0, _, _, _, _, _, hq, hr⟩
  | succ k ihk =>
    intro c s hk hr hq
    obtain ⟨c', hc'⟩ := hR.progress hr h1
    cases hc' with
    | @move b src dst its m w =>
      obtain ⟨n1, c'', hs, hq', -⟩ := hQ s _ _ hq MStep.move
      cases hs
      obtain ⟨n2, b', a', its', m', w', hq3, hr3⟩ :=
        ihk _ _ (by simp [MConf.measure] at hk ⊢; omega) (hR.move hr) hq'
      exact ⟨n1 + n2, b', a', its', m', w', by rw [iterN_add]; exact hq3, hr3⟩
    | op =>
      obtain ⟨-, hk', -⟩ := hR.at_op hr
      rw [← hk'] at hr hq
      exact ⟨0, _, _, _, _, _, hq, hr⟩

end

end Backend.Proof
