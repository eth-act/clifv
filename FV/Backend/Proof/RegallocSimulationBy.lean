import FV.Backend.Proof.RegallocFwd
import FV.Backend.Proof.PerEdgeRegallocFwd

/-!
# Allocation simulations over any deterministic code step

The legacy allocation simulation (`IsSimulation`, over `VStep`) and the per-successor one
(`PerEdge.IsSimulation`, over `VStepAt edges`) differ only in the code step. `IsSimulationBy`
takes that step as a parameter; both existing structures convert to and from it, so their
statements are unchanged. The forward-realization lemmas are proved once for every deterministic
step (`forwardBy`, `forwardBy_op`), so the concrete-machine consumers can serve either form.
-/

namespace Backend.Proof

open Backend

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {sem : ISem V W} {keep : Reg → V → V}

/-- An allocation simulation for an arbitrary code step `vstep`. -/
structure IsSimulationBy (vc : VCode) (rf : RFunc) (sem : ISem V W) (keep : Reg → V → V)
    (vstep : VConf V W → VConf V W → Prop) (R : MConf V W → VConf V W → Prop) : Prop where
  step : ∀ {c v c'},R c v → MStep vc sem keep rf c c' →
    (R c' v ∧ c'.measure < c.measure) ∨ ∃ v',vstep v v' ∧ R c' v'
  progress : ∀ {c v v'},R c v → vstep v v' → ∃ c',MStep vc sem keep rf c c'
  ret : ∀ {vals m w v},R (.ret vals m w) v → v = .ret vals w
  halt : ∀ {w v},R (.halt w) v → v = .halt w
  run : ∀ {s v},R (.run s) v → ∃ s',v = .run s'
  move : ∀ {b src dst its m w v},R (.run ⟨b,.move src dst :: its,m,w⟩) v →
    R (.run ⟨b,its,upd m dst (m src),w⟩) v
  at_op : ∀ {b k a its m w vs},R (.run ⟨b,.op k a :: its,m,w⟩) (.run vs) →
    vs.b = b ∧ vs.k = k ∧ vs.w = w

theorem IsSimulation.toBy {R : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep R) :
    IsSimulationBy vc rf sem keep (VStep vc sem) R :=
  ⟨hR.step,hR.progress,hR.ret,hR.halt,hR.run,hR.move,hR.at_op⟩

theorem IsSimulationBy.toLegacy {R : MConf V W → VConf V W → Prop}
    (hR : IsSimulationBy vc rf sem keep (VStep vc sem) R) : IsSimulation vc rf sem keep R :=
  ⟨hR.step,hR.progress,hR.ret,hR.halt,hR.run,hR.move,hR.at_op⟩

theorem PerEdge.IsSimulation.toBy {edges : Array (Array (Array Reg))} {R : MConf V W → VConf V W → Prop}
    (hR : PerEdge.IsSimulation vc rf sem keep edges R) :
    IsSimulationBy vc rf sem keep (VStepAt vc edges sem) R :=
  ⟨hR.step,hR.progress,hR.ret,hR.halt,hR.run,hR.move,hR.at_op⟩

theorem IsSimulationBy.toPerEdge {edges : Array (Array (Array Reg))} {R : MConf V W → VConf V W → Prop}
    (hR : IsSimulationBy vc rf sem keep (VStepAt vc edges sem) R) :
    PerEdge.IsSimulation vc rf sem keep edges R :=
  ⟨hR.step,hR.progress,hR.ret,hR.halt,hR.run,hR.move,hR.at_op⟩

theorem forwardBy_aux {vstep : VConf V W → VConf V W → Prop}
    (det : ∀ v v1 v2,vstep v v1 → vstep v v2 → v1 = v2)
    {R : MConf V W → VConf V W → Prop} (hR : IsSimulationBy vc rf sem keep vstep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {v v' : VConf V W} (hv : Star vstep v v') :
    ∀ k (c : MConf V W) s,c.measure ≤ k → R c v → Q s c →
      ∃ n c',Q (iterN step n s) c' ∧ R c' v' ∧ ∀ i < n,T (iterN step i s) := by
  induction hv with
  | refl => exact fun _ c s _ hr hq => ⟨0,c,hq,hr,fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | @step v v1 v' h1 _ ih =>
    intro k
    induction k with
    | zero =>
      intro c s hk hr hq
      obtain ⟨c',hc'⟩ := hR.progress hr h1
      obtain ⟨n1,c'',hs,hq',ht1⟩ := hQ s c c' hq hc'
      rcases hR.step hr hs with ⟨_,hlt⟩ | ⟨v'',hv'',hr''⟩
      · omega
      · rw [det _ _ _ hv'' h1] at hr''
        obtain ⟨n2,c3,hq3,hr3,ht2⟩ := ih c''.measure c'' _ (Nat.le_refl _) hr'' hq'
        exact ⟨n1 + n2,c3,by rw [iterN_add]; exact hq3,hr3,trace_add ht1 ht2⟩
    | succ k ihk =>
      intro c s hk hr hq
      obtain ⟨c',hc'⟩ := hR.progress hr h1
      obtain ⟨n1,c'',hs,hq',ht1⟩ := hQ s c c' hq hc'
      rcases hR.step hr hs with ⟨hr'',hlt⟩ | ⟨v'',hv'',hr''⟩
      · obtain ⟨n2,c3,hq3,hr3,ht2⟩ := ihk c'' _ (by omega) hr'' hq'
        exact ⟨n1 + n2,c3,by rw [iterN_add]; exact hq3,hr3,trace_add ht1 ht2⟩
      · rw [det _ _ _ hv'' h1] at hr''
        obtain ⟨n2,c3,hq3,hr3,ht2⟩ := ih c''.measure c'' _ (Nat.le_refl _) hr'' hq'
        exact ⟨n1 + n2,c3,by rw [iterN_add]; exact hq3,hr3,trace_add ht1 ht2⟩

/-- **Forward simulation** for any deterministic code step: every code run from a related
configuration is realized by the concrete machine, with the trace invariant on the way. -/
theorem forwardBy {vstep : VConf V W → VConf V W → Prop}
    (det : ∀ v v1 v2,vstep v v1 → vstep v v2 → v1 = v2)
    {R : MConf V W → VConf V W → Prop} (hR : IsSimulationBy vc rf sem keep vstep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {v v' : VConf V W} (hv : Star vstep v v') {c : MConf V W} {s : S}
    (hr : R c v) (hq : Q s c) :
    ∃ n c',Q (iterN step n s) c' ∧ R c' v' ∧ ∀ i < n,T (iterN step i s) :=
  forwardBy_aux (vstep := vstep) det hR hQ hv _ c s (Nat.le_refl _) hr hq

/-- At a code state that can step, the machine can be advanced past the pending moves to the
instruction item itself. -/
theorem forwardBy_op {vstep : VConf V W → VConf V W → Prop}
    {R : MConf V W → VConf V W → Prop} (hR : IsSimulationBy vc rf sem keep vstep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {vs : VState V W} {v1 : VConf V W} (h1 : vstep (.run vs) v1) :
    ∀ k (c : MConf V W) s,c.measure ≤ k → R c (.run vs) → Q s c →
      ∃ n b a its m w,Q (iterN step n s) (.run ⟨b,.op vs.k a :: its,m,w⟩) ∧
        R (.run ⟨b,.op vs.k a :: its,m,w⟩) (.run vs) := by
  intro k
  induction k with
  | zero =>
    intro c s hk hr hq
    obtain ⟨c',hc'⟩ := hR.progress hr h1
    cases hc' with
    | move => simp [MConf.measure] at hk
    | op =>
      obtain ⟨-,hk',-⟩ := hR.at_op hr
      rw [← hk'] at hr hq
      exact ⟨0,_,_,_,_,_,hq,hr⟩
  | succ k ihk =>
    intro c s hk hr hq
    obtain ⟨c',hc'⟩ := hR.progress hr h1
    cases hc' with
    | @move b src dst its m w =>
      obtain ⟨n1,c'',hs,hq',-⟩ := hQ s _ _ hq MStep.move
      cases hs
      obtain ⟨n2,b',a',its',m',w',hq3,hr3⟩ :=
        ihk _ _ (by simp [MConf.measure] at hk ⊢; omega) (hR.move hr) hq'
      exact ⟨n1 + n2,b',a',its',m',w',by rw [iterN_add]; exact hq3,hr3⟩
    | op =>
      obtain ⟨-,hk',-⟩ := hR.at_op hr
      rw [← hk'] at hr hq
      exact ⟨0,_,_,_,_,_,hq,hr⟩

/-- The generic lemmas specialize to the existing legacy forward simulation. -/
theorem forwardBy_legacy {R : MConf V W → VConf V W → Prop} (hR : IsSimulation vc rf sem keep R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {v v' : VConf V W} (hv : Star (VStep vc sem) v v') {c : MConf V W} {s : S}
    (hr : R c v) (hq : Q s c) :
    ∃ n c',Q (iterN step n s) c' ∧ R c' v' ∧ ∀ i < n,T (iterN step i s) :=
  forwardBy (vstep := VStep vc sem) (fun _ _ _ => VStep_det) hR.toBy hQ hv hr hq

/-- The generic lemmas specialize to per-successor code runs. -/
theorem forwardBy_perEdge {edges : Array (Array (Array Reg))} {R : MConf V W → VConf V W → Prop}
    (hR : PerEdge.IsSimulation vc rf sem keep edges R)
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T)
    {v v' : VConf V W} (hv : Star (VStepAt vc edges sem) v v') {c : MConf V W} {s : S}
    (hr : R c v) (hq : Q s c) :
    ∃ n c',Q (iterN step n s) c' ∧ R c' v' ∧ ∀ i < n,T (iterN step i s) :=
  forwardBy (vstep := VStepAt vc edges sem) (fun _ _ _ => PerEdge.VStepAt_det) hR.toBy hQ hv hr hq

end

end Backend.Proof
