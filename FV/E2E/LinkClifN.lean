import FV.E2E.LinkClif

/-!
# Linking at the CLIF level with bounded callee runs

`linkEnv P base` runs a called function `g` of `P` with unbounded fuel (`runLim`). The Arm-level
linking (`FV/E2E/LinkArm.lean`) is an induction on the whole-program fuel, so it needs the
environment whose program callees run at most `M` steps (`linkEnvN P base M`; a callee that does
not finish within `M` steps is `outOfFuel`, which the caller treats as `stuck`).
`runLoop_linkN`: a complete whole-program run of at most `M + 1` steps is a complete
per-function run under `linkEnvN P base M` (`runLoop_link` with bounded callee runs: every
callee's sub-run is shorter than the whole run).
-/

namespace Clif

/-- **The environment of the per-function programs of `P` with callee runs of at most `M` steps**:
a call of a function `g` of `P` runs `g`'s whole-program run for at most `M` steps; every other
extern is `base`'s. -/
def linkEnvN (P : Program) (base : Env) (M : Nat) : Env where
  extern n := match P.func? n with
    | some _ => some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLoop base P M s
      | .trap c => .trapped c
      | .stuck m => .stuck m
    | none => base.extern n

theorem linkEnvN_none {P : Program} {base : Env} {M : Nat} {n : String} (h : P.func? n = none) :
    (linkEnvN P base M).extern n = base.extern n := by
  simp [linkEnvN, h]

theorem linkEnvN_some {P : Program} {base : Env} {M : Nat} {n : String} {g : Function}
    (h : P.func? n = some g) :
    (linkEnvN P base M).extern n = some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLoop base P M s
      | .trap c => .trapped c
      | .stuck m => .stuck m := by
  simp [linkEnvN, h]

/-- **Linking at the CLIF level with bounded callee runs** (`runLoop_link` with
`linkEnvN P base M`): a complete whole-program run of at most `M + 1` steps is a complete
per-function run whose program callees run at most `M` steps. -/
theorem runLoop_linkN {P : Program} {base : Env} {f : Function} (M : Nat)
    (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs) (hP : ∀ g ∈ P.funcs, LinkFree g) :
    ∀ (N : Nat) (s : State), N ≤ M + 1 → LInv P s →
      (∀ msg, runLoop base P N s ≠ .stuck msg) → runLoop base P N s ≠ .outOfFuel →
      ∃ m, runLoop (linkEnvN P base M) (P.only f) m s = runLoop base P N s := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s hNM hI hst hof
  cases N with
  | zero => exact absurd rfl hof
  | succ N =>
  -- a per-function step `r` after which the whole-program run continues with `n` steps
  have helper : ∀ (r : StepResult) (n : Nat), n < N + 1 →
      step (linkEnvN P base M) (P.only f) s = r → runLoop base P (N + 1) s = afterStep base P n r →
      (∀ s1, r = .next s1 → LInv P s1) →
      ∃ m, runLoop (linkEnvN P base M) (P.only f) m s = runLoop base P (N + 1) s := by
    intro r n hn hr hrun hinv
    cases r with
    | next s1 =>
      rw [hrun] at hst hof ⊢
      obtain ⟨m, hm⟩ := ih n hn s1 (by omega) (hinv s1 rfl) hst hof
      exact ⟨m + 1, by rw [runLoop_succ', hr]; exact hm⟩
    | _ => exact ⟨0 + 1, by rw [runLoop_succ', hr, hrun]; rfl⟩
  -- the steps that do not call another function of `P` are the same
  have same : step (linkEnvN P base M) (P.only f) s = step base P s →
      ∃ m, runLoop (linkEnvN P base M) (P.only f) m s = runLoop base P (N + 1) s := fun h =>
    helper _ N (by omega) h (runLoop_succ' ..) fun s1 hs1 => (step_next_linv hP hI hs1).1
  -- a call (`callCont`) from `t`, whose frame is `s`'s up to `regs`/`body`/`term`
  have call : ∀ (t : State) rest rs ext vals, t.callers = s.callers → t.mem = s.mem →
      (∀ regs, LFrame P { t.frame with regs, body := rest }) →
      step base P s = Opt.callCont base P t rest rs ext vals →
      step (linkEnvN P base M) (P.only f) s = Opt.callCont (linkEnvN P base M) (P.only f) t rest rs ext vals →
      ∃ m, runLoop (linkEnvN P base M) (P.only f) m s = runLoop base P (N + 1) s := by
    intro t rest rs ext vals htc htm hfr e1 e2
    cases hpf : P.func? ext.name with
    | none =>
      have hfn : f.name ≠ ext.name := Program.func?_none hpf f hf
      apply same
      rw [e1, e2]
      simp only [Opt.callCont, hpf, Program.only_func?, hfn, ↓reduceIte, linkEnvN_none hpf]
    | some g =>
      obtain ⟨hgP, hgn⟩ := Program.func?_some hpf
      by_cases hgf : g = f
      · subst hgf
        apply same
        rw [e1, e2]
        simp only [Opt.callCont, hpf, Program.only_func?, hgn, ↓reduceIte]
      have hfn : f.name ≠ ext.name := fun h => hgf (name_inj hnd hgP hf (hgn.trans h.symm))
      -- the per-function step: the atomic call of `g`
      have e2' := e2
      simp only [Opt.callCont, Program.only_func?, hfn, ↓reduceIte, linkEnvN_some hpf] at e2'
      rw [runLoop_succ', e1] at hst hof
      rw [runLoop_succ', e1]
      simp only [Opt.callCont, hpf] at hst hof ⊢
      cases hsig : (AbiParam.tys g.sig.params == AbiParam.tys ext.sig.params &&
          AbiParam.tys g.sig.returns == AbiParam.tys ext.sig.returns) with
      | false =>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, afterStep] at hst
        exact absurd rfl (hst _)
      | true =>
        simp only [hsig, ↓reduceIte] at hst hof ⊢
        simp only [Bool.and_eq_true, beq_iff_eq] at hsig
        cases he : enterFunc g vals t.mem with
        | trap c => exact absurd he (Opt.enterFunc_not_trap g vals t.mem c)
        | stuck m =>
          rw [he] at hst; exact absurd rfl (hst m)
        | ok a =>
          obtain ⟨fr', mem'⟩ := a
          rw [he] at hst hof
          simp only [StepResult.ofRes_ok, afterStep] at hst hof ⊢
          have hinit : initState P ext.name vals t.mem = .ok ⟨fr', [], mem'⟩ := by
            simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
          rw [hinit] at e2'
          simp only at e2'
          let K : List (Frame × List ValueId) := ({ t.frame with body := rest }, rs) :: t.callers
          have hK : ({ frame := fr', callers := K, mem := mem' } : State) =
              (⟨fr', [], mem'⟩ : State).below K := rfl
          have hsubI : LInv P ⟨fr', [], mem'⟩ :=
            ⟨LFrame.enterFunc hgP he, fun _ h => by cases h⟩
          have hfr' : fr'.func = g := by
            obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
            rw [hfr]
          rw [hK] at hst hof ⊢
          cases hsub : runLoop base P N ⟨fr', [], mem'⟩ with
          | returned rvals mem2 =>
            obtain ⟨j, hj0, hjN, hj⟩ := runLoop_below_returned base P N _ rvals mem2 hsub
            have hN : N = (N - j) + j := by omega
            rw [hN, hj] at hst hof ⊢
            have hlim : runLoop base P M ⟨fr', [], mem'⟩ = .returned rvals mem2 := by
              rw [show M = N + (M - N) by omega,
                runLoop_add base P N _ (by rw [hsub]; exact fun h => by cases h)]
              exact hsub
            have hty := runLoop_returned_tys hP N _ rvals mem2 hsubI hsub
            simp only [State.bottom, List.getLast?_nil, Option.map_none, Option.getD_none,
              hfr'] at hty
            rw [hlim] at e2'
            simp only [hty, hsig.2, beq_self_eq_true, ↓reduceIte] at e2'
            -- resume the caller
            cases hset : t.frame.regs.setMany rs rvals with
            | none =>
              simp only [resumeStep, K, hset, afterStep] at hst
              exact absurd rfl (hst _)
            | some regs =>
              have hc : continueWith t rest rs rvals mem2 =
                  .next ⟨{ t.frame with regs, body := rest }, t.callers, mem2⟩ := by
                simp only [continueWith, hset]
              rw [hc] at e2'
              have hres : resumeStep K rvals mem2 =
                  .next ⟨{ t.frame with regs, body := rest }, t.callers, mem2⟩ := by
                simp only [resumeStep, K, hset]
              rw [hres] at hst hof ⊢
              simp only [afterStep] at hst hof ⊢
              obtain ⟨m, hm⟩ := ih (N - j) (by omega)
                ⟨{ t.frame with regs, body := rest }, t.callers, mem2⟩ (by omega)
                ⟨hfr regs, by rw [htc]; exact hI.2⟩ hst hof
              exact ⟨m + 1, by rw [runLoop_succ', e2']; exact hm⟩
          | trapped c =>
            have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hst hof ⊢
            have hlim : runLoop base P M ⟨fr', [], mem'⟩ = .trapped c := by
              rw [show M = N + (M - N) by omega,
                runLoop_add base P N _ (by rw [hsub]; exact fun h => by cases h)]
              exact hsub
            rw [hlim] at e2'
            exact ⟨1, by rw [runLoop_succ', e2']; rfl⟩
          | stuck msg =>
            have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hst
            exact absurd rfl (hst msg)
          | outOfFuel =>
            have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hof
            exact absurd rfl hof
  by_cases hT : ∃ fn args et, s.frame.body = [] ∧ s.frame.term = .tryCall fn args et
  · -- a `try_call`: its preludes are the same, then the call from the waiting frame
    obtain ⟨fn, args, et, hb, ht⟩ := hT
    have e1 := step_try base P s hb ht
    have e2 := step_try (linkEnvN P base M) (P.only f) s hb ht
    rcases ofRes_cases (tryPre s.frame fn et) _ _ with h1 | ⟨⟨n, b, bc⟩, h1, h1'⟩
    · exact same (by rw [e1, e2]; exact h1.symm)
    rw [h1] at e1
    rw [h1'] at e2
    dsimp only at e1 e2
    rcases ofRes_cases (Opt.callArgs (tryState s bc).frame fn args) _ _ with h2 | ⟨⟨ext, vals⟩, h2, h2'⟩
    · exact same (by rw [e1, e2]; exact h2.symm)
    rw [h2] at e1
    rw [h2'] at e2
    dsimp only at e1 e2
    exact call (tryState s bc) [] _ ext vals rfl rfl (fun regs => LFrame.jump hI.1.1 regs bc) e1 e2
  have hnt : ∀ fn args et, s.frame.body = [] → s.frame.term ≠ .tryCall fn args et :=
    fun fn args et hb ht => hT ⟨fn, args, et, hb, ht⟩
  have hci := hI.1.headNoCI hP hnt
  have e1 := Opt.step_eq_lift base P s hci
  have e2 := Opt.step_eq_lift (linkEnvN P base M) (P.only f) s hci
  cases hl : Opt.lstep s.frame s.mem with
  | next fr1 m1 => exact same (by rw [e1, e2, hl]; rfl)
  | ret vals => exact same (by rw [e1, e2, hl]; rfl)
  | trap c => exact same (by rw [e1, e2, hl]; rfl)
  | stuck m => exact same (by rw [e1, e2, hl]; rfl)
  | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
  | call ext vals rs rest =>
    rw [hl] at e1 e2
    obtain ⟨st, fn, args, hb, -, -, -⟩ := Opt.lstep_call_inv hl
    exact call s rest rs ext vals rfl rfl (fun regs => hI.1.rest hb regs) e1 e2


end Clif
