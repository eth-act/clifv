import FV.Opt.Proof.SemSimMU
import FV.Clif.LinkClifXN

/-!
# Memory-aware simulations keep the call depth (#1119)

`runLoopX_refinesSRMU` with the call depth: from `SRMU`-related states, a source run with
unwinding that ends (returns, traps or unwinds) is matched by a target run with the same outcome,
and if every state the source run reaches (`Clif.ReachesX`) has at most `d` callers, so has every
state the target run reaches. Related states have callers of the same length
(`CallersRelMU.length`) and the target's stuttering steps keep the callers (`Stut.callers`).

* **`runLoopX_refinesSRMU_depth`**;
* `reachesX_toX_of_reaches`, `reaches_of_reachesX_toX`: for an environment of `Clif.run`
  (`Env.toX`, never unwinding), reachability with unwinding is plain reachability
  (`Clif.Reaches`, the one of `Clif.DepthLe`).
-/

namespace Opt

open Clif

/-- A state reached with unwinding from the start of stuttering target steps is on them (with the
start's callers) or reached from their end. -/
theorem Stut.reachesX_split {env : XEnv} {q : Program} {s s2 : State} (h : Stut env.toEnv q s s2)
    (ts : List (Option ExnTable)) {ys : XState} (hr : ReachesX env q ⟨s, ts⟩ ys) :
    ys.s.callers = s.callers ∨ ReachesX env q ⟨s2, ts⟩ ys := by
  induction h generalizing ys with
  | refl => exact .inr hr
  | step h1 hc _ ih =>
    cases hr with
    | refl => exact .inl rfl
    | next hs hr' =>
      rw [stepX_of_same ts h1 hc] at hs
      simp only [XStepResult.next.injEq] at hs
      subst hs
      rcases ih hr' with h | h
      · exact .inl (h.trans hc)
      · exact .inr h

/-- **`runLoopX_refinesSRMU` keeping the call depth**: from `SRMU`-related states the runs with
unwinding refine, and when the source run ends (neither `stuck` nor out of fuel) with every state
it reaches having at most `d` callers, every state the target run reaches has at most `d`
callers. -/
theorem runLoopX_refinesSRMU_depth {syms : String → Option Nat} {env : XEnv}
    (hE : EnvKeepsSymbolsX env) {p q : Program} (hP : FunsSimMU p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRMU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') ∧
        ((∀ msg, Clif.runLoopX env p n xs ≠ .stuck msg) → Clif.runLoopX env p n xs ≠ .outOfFuel →
          ∀ d, (∀ ys, ReachesX env p xs ys → ys.s.callers.length ≤ d) →
          ∀ ys', ReachesX env q xs' ys' → ys'.s.callers.length ≤ d) := by
  intro n
  induction n with
  | zero =>
    intro xs xs' _
    exact ⟨0, ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩,
      fun _ hof => (hof rfl).elim⟩
  | succ n ih =>
    intro xs xs' h
    obtain ⟨s', ts'⟩ := xs'
    have hlen : s'.callers.length = xs.s.callers.length := h.callers.length
    have hb0 : ∀ d, (∀ ys, ReachesX env p xs ys → ys.s.callers.length ≤ d) →
        s'.callers.length ≤ d := fun d hdd => by
      have := hdd xs (.refl _); omega
    rcases sim_stepMU hE hP h with ⟨xs1, s1', hst, hstut, hr⟩ | ⟨s2, hstut, hr⟩
    · obtain ⟨n1, hn1, hd1⟩ := ih xs1 _ hr
      obtain ⟨k, hk⟩ := hstut.runLoopX ts'
      refine ⟨n1 + k, ?_, fun hns hof d hdd ys' hy => ?_⟩
      · rw [hk, runLoopX_of_next hst]
        exact hn1
      · rw [runLoopX_of_next hst] at hns hof
        rcases hstut.reachesX_split ts' hy with hc | hy1
        · rw [hc]; exact hb0 d hdd
        · exact hd1 hns hof d (fun ys hy => hdd ys (.next hst hy)) ys' hy1
    · obtain ⟨hn, hdn, ht, hu⟩ := hr
      obtain ⟨k, hk⟩ := hstut.runLoopX ts'
      have hc2 : s2.callers = s'.callers := hstut.callers
      -- a state reached from the end `s2` of the stuttering steps whose step is not `next` is `s2`
      have hend : ∀ d, (∀ ys, ReachesX env p xs ys → ys.s.callers.length ≤ d) →
          (∀ xs2, stepX env q ⟨s2, ts'⟩ ≠ .next xs2) →
          ∀ ys', ReachesX env q ⟨s', ts'⟩ ys' → ys'.s.callers.length ≤ d := by
        intro d hdd hnx ys' hy
        rcases hstut.reachesX_split ts' hy with hc | hy2
        · rw [hc]; exact hb0 d hdd
        · cases hy2 with
          | refl => show s2.callers.length ≤ d; rw [hc2]; exact hb0 d hdd
          | next hs2 _ => exact absurd hs2 (hnx _)
      rw [Clif.runLoopX]
      cases hs : stepX env p xs with
      | next xs1 =>
        obtain ⟨xs1', hs', hr'⟩ := hn xs1 hs
        obtain ⟨n1, hn1, hd1⟩ := ih _ _ hr'
        refine ⟨n1 + 1 + k, ?_, fun hns hof d hdd ys' hy => ?_⟩
        · rw [hk, runLoopX_of_next hs']
          exact hn1
        · rcases hstut.reachesX_split ts' hy with hc | hy2
          · rw [hc]; exact hb0 d hdd
          · cases hy2 with
            | refl => show s2.callers.length ≤ d; rw [hc2]; exact hb0 d hdd
            | next hs2 hy3 =>
              rw [hs'] at hs2
              simp only [XStepResult.next.injEq] at hs2
              subst hs2
              exact hd1 hns hof d (fun ys hy => hdd ys (.next hs hy)) ys' hy3
      | done vs m =>
        refine ⟨0 + 1 + k, ?_, fun _ _ d hdd => hend d hdd (fun _ h2 => ?_)⟩
        · rw [hk, Clif.runLoopX, hdn vs m hs]
          exact ⟨fun _ _ h => h, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
        · rw [hdn vs m hs] at h2; cases h2
      | trapped c =>
        refine ⟨0 + 1 + k, ?_, fun _ _ d hdd => hend d hdd (fun _ h2 => ?_)⟩
        · rw [hk, Clif.runLoopX, ht c hs]
          exact ⟨fun _ _ h => (by cases h), fun _ h => h, fun _ _ h => (by cases h)⟩
        · rw [ht c hs] at h2; cases h2
      | unwound e m =>
        refine ⟨0 + 1 + k, ?_, fun _ _ d hdd => hend d hdd (fun _ h2 => ?_)⟩
        · rw [hk, Clif.runLoopX, hu e m hs]
          exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => h⟩
        · rw [hu e m hs] at h2; cases h2
      | stuck m =>
        exact ⟨0, ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩,
          fun hns _ => (hns m rfl).elim⟩

/-- For an environment of `Clif.run`, a plain step that continues is a step with unwinding. -/
theorem stepX_toX_of_next {env : Env} {q : Program} {s s' : State} (h : step env q s = .next s')
    (ts : List (Option ExnTable)) :
    stepX env.toX q ⟨s, ts⟩ = liftStep ⟨s, ts⟩ (.next s') := by
  have hns : ∀ msg, step env.toX.toEnv q (⟨s, ts⟩ : XState).s ≠ .stuck msg := by
    intro msg hm
    rw [Env.toX_toEnv] at hm
    change step env q s = .stuck msg at hm
    rw [h] at hm
    cases hm
  rw [stepX_of_not_stuck hns, Env.toX_toEnv]
  change liftStep ⟨s, ts⟩ (step env q s) = _
  rw [h]

/-- For an environment of `Clif.run`, a state plainly reachable is reachable with unwinding. -/
theorem reachesX_toX_of_reaches {env : Env} {q : Program} {s u : State}
    (h : Clif.Reaches env q s u) :
    ∀ ts, ∃ ts', ReachesX env.toX q ⟨s, ts⟩ ⟨u, ts'⟩ := by
  induction h with
  | refl s => exact fun ts => ⟨ts, .refl _⟩
  | @next s s' _ h1 _ ih =>
    intro ts
    obtain ⟨ts', h'⟩ := ih (if s'.callers.length = s.callers.length + 1 then pendingOf s :: ts
      else if s'.callers.length + 1 = s.callers.length then ts.tail else ts)
    exact ⟨ts', .next (stepX_toX_of_next h1 ts) h'⟩

/-- For an environment of `Clif.run`, a state reachable with unwinding is plainly reachable. -/
theorem reaches_of_reachesX_toX {env : Env} {p : Program} {xs ys : XState}
    (h : ReachesX env.toX p xs ys) : Clif.Reaches env p xs.s ys.s := by
  induction h with
  | refl => exact .refl _
  | @next xs xs' _ h1 _ ih =>
    have hx : stepX env.toX p xs = liftStep xs (step env p xs.s) := by
      simp only [stepX, raiseAt_of_noUnwind (Env.toX_noUnwind env), Env.toX_toEnv]
    rw [hx] at h1
    cases hs : step env p xs.s with
    | next s1 =>
      rw [hs] at h1
      simp only [liftStep, XStepResult.next.injEq] at h1
      subst h1
      exact .next hs ih
    | done v m => rw [hs] at h1; simp [liftStep] at h1
    | trapped c => rw [hs] at h1; simp [liftStep] at h1
    | stuck m => rw [hs] at h1; simp [liftStep] at h1

end Opt
