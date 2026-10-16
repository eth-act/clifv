import FV.E2E.LinkClifRev
import FV.Clif.LinkClifXN

/-!
# Unlinking runs with unwinding (S10f, #233)

`runLoopX_linkR` (`FV/Clif/LinkClifXN.lean`) turns a complete whole-program run with unwinding into
a per-function run of `P.bare` whose calls of `P`'s functions are atomic. Here the converse
(`FV/E2E/LinkClifRev.lean`'s `unlink_run` with unwinding), for any environment `E` that
**unlinks** `P` over the base environment `B` (`UnlinkX`: each function `h` of `P` is an extern of
`E` whose returns, traps and exceptions are those of `h`'s whole-program run with unwinding, every
other extern is `B`'s; `P`'s functions' names first, then names of `P` and `B`):

* `unlinkX_step`: a per-function step from a state without callers that is not stuck is
  followed by the whole program (`XFollows`: the whole program reaches a state whose step has the
  same result — a callee entered, run to its end, its result taken back, or its exception
  propagated into the caller's frame);
* `unlinkX_run`: a per-function run that returns, traps or unwinds is a whole-program run with
  the same outcome; `unlinkX_reach`: every state it reaches is reached by the whole program.

Indirect calls need `UnlinkIndX` (`IndScopeX`; `B` knows no signature).
-/

namespace Clif

/-! ## Unlinking environments -/

/-- **`E` unlinks `P` over `B`, with unwinding**: distinct names, no `return_call`, declarations of
`P`'s functions with their signatures, each function `h` of `P` an extern of `E` whose returns,
traps and exceptions are those of `h`'s whole-program run with unwinding, every other extern
`B`'s, the names of `P`'s functions first, then names of `P` and of `B`, the signatures of `P`'s
functions only. -/
structure UnlinkX (E : XEnv) (P : Program) (B : XEnv) : Prop where
  nd : (P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ P.funcs, LinkFree g
  decl : ∀ g ∈ P.funcs, ∀ fn e, g.extern? fn = some e → ∀ h, P.func? e.name = some h → h.sig = e.sig
  prog : ∀ h ∈ P.funcs, ∃ hs, E.extern h.name = some hs ∧ ∀ vals mem (o : XOutcome),
    hs vals mem = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
    ∃ fr' mem', enterFunc h vals mem = .ok (fr', mem') ∧
      ∃ N, runLoopX B P N ⟨⟨fr', [], mem'⟩, []⟩ = o
  base : ∀ n, P.func? n = none → E.extern n = B.extern n
  names : ∃ rest, E.names = P.funcs.map (·.name) ++ rest ∧ ∀ n ∈ rest, n ∈ P.externNames ++ B.names
  sigOf : ∀ n, E.sigOf n = (P.func? n).map (·.sig)

/-- For indirect calls: aliases are one extern of `B` (`IndScopeX`), `B` knows no signature. -/
structure UnlinkIndX (P : Program) (B : XEnv) (syms : String → Option Nat) : Prop where
  scope : IndScopeX P B syms
  baseSig : ∀ n, B.sigOf n = none

/-- **The whole program follows the step result `r`** from `xs`: it reaches a state whose step
is `r`. -/
def XFollows (B : XEnv) (P : Program) (xs : XState) (r : XStepResult) : Prop :=
  ∃ u, ReachesX B P xs u ∧ stepX B P u = r

/-! ## Runs and reachable states -/

theorem runLoopX_trapped_reaches (env : XEnv) (p : Program) :
    ∀ (N : Nat) (xs : XState) (c : TrapCode), runLoopX env p N xs = .trapped c →
      ∃ u, ReachesX env p xs u ∧ stepX env p u = .trapped c
  | 0, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, c, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env p xs with
    | next xs1 =>
      rw [hs] at h
      obtain ⟨u, hu, hd⟩ := runLoopX_trapped_reaches env p N xs1 c h
      exact ⟨u, .next hs hu, hd⟩
    | trapped c' =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.trapped.injEq] at h
      subst h
      exact ⟨xs, .refl _, hs⟩
    | _ => rw [hs] at h; cases h

theorem ReachesX.runLoopX {env : XEnv} {p : Program} {xs u : XState} (h : ReachesX env p xs u) :
    ∃ k, ∀ n, Clif.runLoopX env p (n + k) xs = Clif.runLoopX env p n u := by
  induction h with
  | refl => exact ⟨0, fun _ => rfl⟩
  | next hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n => ?_⟩
    rw [show n + (k + 1) = (n + k) + 1 by omega, runLoopX_succ', hs]
    exact hk n

theorem XFollows.after {B : XEnv} {P : Program} {xs : XState} {r : XStepResult}
    (h : XFollows B P xs r) : ∃ k, ∀ n, runLoopX B P (n + 1 + k) xs = afterStepX B P n r := by
  obtain ⟨u, hu, hs⟩ := h
  obtain ⟨k, hk⟩ := hu.runLoopX
  exact ⟨k, fun n => by rw [hk (n + 1), runLoopX_succ', hs]⟩

/-! ## Indirect calls of externs -/

/-- An indirect call to no function of `P`: where the per-function call (names of `P` and `B`)
returns, traps or raises, the whole program's does the same (aliases are one extern of `B`,
neither knows a signature). -/
theorem unlinkX_externAt {E B : XEnv} {P : Program} {syms : String → Option Nat}
    (hU : UnlinkX E P B) (hJ : UnlinkIndX P B syms) {mem : Mem} (hm : mem.symbols = syms)
    {d : Signature} {a : Nat} {v : List Val}
    (hnone : P.funcs.find? (fun g => mem.symbols g.name == some a) = none) :
    (∀ q, callExternAt E.toEnv P.bare mem d a v = .ok q → callExternAt B.toEnv P mem d a v = .ok q) ∧
    (∀ c, callExternAt E.toEnv P.bare mem d a v = .trap c →
      callExternAt B.toEnv P mem d a v = .trap c) ∧
    (∀ em, externAtRaise E P.bare mem d a v = some em → externAtRaise B P mem d a v = some em) ∧
    (∀ em, externAtRaise B P mem d a v = some em → externAtRaise E P.bare mem d a v = some em ∨
      ∃ msg, callExternAt E.toEnv P.bare mem d a v = .stuck msg) := by
  obtain ⟨rest, hn, hrest⟩ := hU.names
  have hsame : ∀ n₁, (E.names ++ P.bare.externNames).find? (fun n => mem.symbols n == some a) =
      some n₁ → ∃ n₂, (B.names ++ P.externNames).find? (fun n => mem.symbols n == some a) =
        some n₂ ∧ E.extern n₁ = B.extern n₂ ∧ E.sigOf n₁ = none ∧ B.sigOf n₂ = none := by
    intro n₁ h₁
    have hq₁ : mem.symbols n₁ = some a := by simpa using List.find?_some h₁
    have hm₁ := List.mem_of_find?_eq_some h₁
    rw [Program.bare_externNames, List.append_nil, hn] at hm₁
    have hp₁ := func?_none_of_find hnone hq₁
    have hin : n₁ ∈ B.names ++ P.externNames := by
      rcases List.mem_append.mp hm₁ with h | h
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
        have := List.find?_eq_none.mp hnone g hg
        simp [hq₁] at this
      · rcases List.mem_append.mp (hrest n₁ h) with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ h
    cases h₂ : (B.names ++ P.externNames).find? (fun n => mem.symbols n == some a) with
    | none => exact absurd (List.find?_eq_none.mp h₂ n₁ hin) (by simp [hq₁])
    | some n₂ =>
      have hq₂ : mem.symbols n₂ = some a := by simpa using List.find?_some h₂
      have hm₂ := List.mem_of_find?_eq_some h₂
      have hp₂ := func?_none_of_find hnone hq₂
      have hn₂ : n₂ ∈ P.names ++ B.names := by
        rcases List.mem_append.mp hm₂ with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (names_extern h)
      have hn₁ : n₁ ∈ P.names ++ B.names := by
        rcases List.mem_append.mp hin with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (names_extern h)
      rw [hm] at hq₁ hq₂
      refine ⟨n₂, rfl, ?_, by rw [hU.sigOf, hp₁]; rfl, hJ.baseSig n₂⟩
      rw [hU.base n₁ hp₁]
      exact hJ.scope.alias n₁ hn₁ n₂ hn₂ a hq₁ hq₂ hp₁ hp₂
  refine ⟨fun q h => ?_, fun c h => ?_, fun em h => ?_, fun em h => ?_⟩
  · obtain ⟨n₁, g, h₁, hg, -, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp h
    obtain ⟨n₂, h₂, hx, -, hs₂⟩ := hsame n₁ h₁
    refine callExternAt_ok_iff.mpr ⟨n₂, g, h₂, ?_, by simp [XEnv.toEnv, hs₂], hv, rv, m', ho, hrt,
      rfl⟩
    have : E.toEnv.extern n₁ = B.toEnv.extern n₂ := by simp only [XEnv.toEnv, hx]
    rw [← this]; exact hg
  · obtain ⟨n₁, g, h₁, hg, -, hv, ho⟩ := callExternAt_trap_iff.mp h
    obtain ⟨n₂, h₂, hx, -, hs₂⟩ := hsame n₁ h₁
    refine callExternAt_trap_iff.mpr ⟨n₂, g, h₂, ?_, by simp [XEnv.toEnv, hs₂], hv, ho⟩
    have : E.toEnv.extern n₁ = B.toEnv.extern n₂ := by simp only [XEnv.toEnv, hx]
    rw [← this]; exact hg
  · unfold externAtRaise at h ⊢
    cases h₁ : (E.names ++ P.bare.externNames).find? (fun n => mem.symbols n == some a) with
    | none => rw [h₁] at h; cases h
    | some n₁ =>
      obtain ⟨n₂, h₂, hx, hs₁, hs₂⟩ := hsame n₁ h₁
      rw [h₁] at h
      rw [h₂]
      dsimp only at h ⊢
      rw [hx, hs₁] at h
      rw [hs₂]
      exact h
  · cases h₁ : (E.names ++ P.bare.externNames).find? (fun n => mem.symbols n == some a) with
    | none =>
      refine .inr ⟨"call_indirect: no function at the callee address", ?_⟩
      have h₁' : E.toEnv.names.find? (fun n => mem.symbols n == some a) = none := by
        simpa [XEnv.toEnv] using h₁
      simp [callExternAt, h₁', Res.ofOption]
    | some n₁ =>
      left
      obtain ⟨n₂, h₂, hx, hs₁, hs₂⟩ := hsame n₁ h₁
      unfold externAtRaise at h ⊢
      rw [h₂] at h
      rw [h₁]
      dsimp only at h ⊢
      rw [hx, hs₁]
      rw [hs₂] at h
      exact h

/-- A per-function step from a state without callers of a frame of `f` that continues leaves no
caller and no pending table, in a frame of `f`. -/
theorem stepX_bare_next {E : XEnv} {P : Program} {f : Function} (hfree : LinkFree f) {s : State}
    (hfr : LFrame (P.only f) s.frame) (hc : s.callers = []) {xs1 : XState}
    (h : stepX E P.bare ⟨s, []⟩ = .next xs1) :
    xs1.s.callers = [] ∧ xs1.tries = [] ∧ LFrame (P.only f) xs1.s.frame := by
  have hPf : ∀ g ∈ (P.only f).funcs, LinkFree g := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hfree
  have hX : XInv (P.only f) ⟨s, []⟩ :=
    ⟨⟨hfr, by rw [hc]; exact fun _ h => nomatch h⟩, by simp [XState.Aligned, hc]⟩
  have hX1 := stepX_next_xinv hPf hX h (fun _ h => by simp at h)
  have hcl : xs1.s.callers = [] := by
    unfold stepX at h
    split at h
    · unfold raiseIn at h
      split at h
      · rename_i r _
        cases r with
        | ok fr => simp only [XStepResult.ofRes, XStepResult.next.injEq] at h; subst h; exact hc
        | trap c => cases h
        | stuck m => cases h
      · simp only [hc] at h
        simp [unwindFrom] at h
    · cases hs : step E.toEnv P.bare s with
      | next s1 =>
        rw [hs] at h
        simp only [liftStep, XStepResult.next.injEq] at h
        subst h
        exact step_bare_callers hPf hfr hc hs
      | _ => rw [hs] at h; simp [liftStep] at h
  have ha := hX1.2
  simp only [XState.Aligned, hcl, List.length_nil, List.length_eq_zero_iff] at ha
  exact ⟨hcl, ha, hX1.1.1⟩

/-! ## One step -/

section Step

variable {E B : XEnv} {P : Program} {syms : String → Option Nat} (hU : UnlinkX E P B)
  {f : Function} (hf : f ∈ P.funcs) (hio : ¬ IndFree f → UnlinkIndX P B syms)
include hU hf hio

/-- **One per-function step is followed by the whole program**: from a state without callers of
a frame of `f` (`UInv`), a per-function step that is not stuck has a whole-program counterpart
(`XFollows`). -/
theorem unlinkX_step {s : State} (hI : UInv P f syms s) {r : XStepResult}
    (hr : stepX E P.bare ⟨s, []⟩ = r) (hns : ∀ msg, r ≠ .stuck msg) :
    XFollows B P ⟨s, []⟩ r := by
  have hP := hU.free
  have hff : s.frame.func = f := by simpa [Program.only] using hI.frame.1
  have hIP : LFrame P s.frame := ⟨by rw [hff]; exact hf, hI.frame.2⟩
  have hc := hI.callers
  have same : stepX E P.bare ⟨s, []⟩ = stepX B P ⟨s, []⟩ → XFollows B P ⟨s, []⟩ r :=
    fun h => ⟨_, .refl _, h.symm.trans hr⟩
  -- an atomic call of `g` from `t` (whose frame is `s`'s up to `body`/`term`)
  have atomic : ∀ (t : State) rest rs (g : Function) vals, g ∈ P.funcs →
      t.callers = [] → t.frame.func = s.frame.func → t.frame.regs = s.frame.regs →
      t.frame.slots = s.frame.slots → raiseAt? B P s = none →
      step B.toEnv P s = StepResult.ofRes (enterFunc g vals t.mem) (fun (fr', mem') =>
        .next { frame := fr', callers := [({ t.frame with body := rest }, rs)], mem := mem' }) →
      ∀ hs, E.extern g.name = some hs →
      (∀ rv m2, hs vals t.mem = .returned rv m2 → rv.map (·.ty) = AbiParam.tys g.sig.returns →
        r = liftStep ⟨s, []⟩ (continueWith t rest rs rv m2)) →
      (∀ c, hs vals t.mem = .trapped c → r = .trapped c) →
      (∀ e m, hs vals t.mem = .unwound e m → r = raiseIn ⟨s, []⟩ e m) →
      ((∃ msg, hs vals t.mem = .stuck msg) ∨ hs vals t.mem = .outOfFuel → ∃ msg, r = .stuck msg) →
      XFollows B P ⟨s, []⟩ r := by
    intro t rest rs g vals hgP htc htf htr hts hra e1 hs hEg hR hT hW hS
    have ew : stepX B P ⟨s, []⟩ = liftStep ⟨s, []⟩ (step B.toEnv P s) := by simp only [stepX, hra]
    obtain ⟨hs', hEg', hprog⟩ := hU.prog g hgP
    rw [hEg] at hEg'
    cases hEg'
    -- the whole program enters `g`
    have enter : ∀ o, hs vals t.mem = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
        ∃ fr' mem', (∃ N, runLoopX B P N ⟨⟨fr', [], mem'⟩, []⟩ = o) ∧
          XInv P ⟨⟨fr', [], mem'⟩, []⟩ ∧ fr'.func = g ∧
          stepX B P ⟨s, []⟩ = .next ((⟨⟨fr', [], mem'⟩, []⟩ : XState).below
            [({ t.frame with body := rest }, rs)] [pendingOf s]) := by
      intro o ho hs1 hs2
      obtain ⟨fr', mem', he, N, hN⟩ := hprog vals t.mem o ho hs1 hs2
      refine ⟨fr', mem', ⟨N, hN⟩, ⟨⟨LFrame.enterFunc hgP he, fun _ h => by cases h⟩, rfl⟩, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
        rw [hfr]
      · rw [ew, e1, he]
        simp only [StepResult.ofRes, liftStep, hc, List.length_cons, List.length_nil]
        rfl
    cases ho : hs vals t.mem with
    | stuck msg =>
      obtain ⟨m', hm'⟩ := hS (.inl ⟨msg, ho⟩)
      exact absurd hm' (hns m')
    | outOfFuel =>
      obtain ⟨m', hm'⟩ := hS (.inr ho)
      exact absurd hm' (hns m')
    | returned rv m2 =>
      obtain ⟨fr', mem', ⟨N, hN⟩, hsubI, hfr', hw1⟩ :=
        enter _ ho (fun _ h => by cases h) (fun h => by cases h)
      have hty := runLoopX_returned_tys hP N _ rv m2 hsubI hN
      simp only [State.bottom, List.getLast?_nil, Option.map_none, Option.getD_none, hfr'] at hty
      have hr' := hR rv m2 ho hty
      obtain ⟨u, hu, hdone⟩ := runLoopX_returned_reaches B P N _ rv m2 hN
      refine ⟨u.below [({ t.frame with body := rest }, rs)] [pendingOf s],
        .next hw1 (hu.under hP _ _ hsubI), ?_⟩
      rw [stepX_below hP (hu.xinv hP hsubI), hdone, hr']
      cases hset : t.frame.regs.setMany rs rv with
      | none =>
        exfalso
        rw [hr'] at hns
        unfold continueWith at hns
        rw [hset] at hns
        exact hns _ rfl
      | some regs =>
        obtain ⟨tf, tc, tm⟩ := t
        simp only at htc hset
        subst htc
        simp [XStepResult.below, resumeStepX, resumeStep, hset, continueWith, liftStep, hc]
    | trapped c =>
      obtain ⟨fr', mem', ⟨N, hN⟩, hsubI, -, hw1⟩ :=
        enter _ ho (fun _ h => by cases h) (fun h => by cases h)
      obtain ⟨u, hu, htr⟩ := runLoopX_trapped_reaches B P N _ c hN
      refine ⟨u.below [({ t.frame with body := rest }, rs)] [pendingOf s],
        .next hw1 (hu.under hP _ _ hsubI), ?_⟩
      rw [stepX_below hP (hu.xinv hP hsubI), htr, hT c ho]
      rfl
    | unwound e m =>
      obtain ⟨fr', mem', ⟨N, hN⟩, hsubI, -, hw1⟩ :=
        enter _ ho (fun _ h => by cases h) (fun h => by cases h)
      obtain ⟨u, hu, hun⟩ := runLoopX_unwound_reaches B P N _ e m hN
      refine ⟨u.below [({ t.frame with body := rest }, rs)] [pendingOf s],
        .next hw1 (hu.under hP _ _ hsubI), ?_⟩
      rw [stepX_below hP (hu.xinv hP hsubI), hun, hW e m ho]
      have := raiseIn_eq_resumeUnwind (xs := ⟨s, []⟩) (c := { t.frame with body := rest }) rs e m
        htf htr hts
      rw [this]
      simp only [hc]
      rfl
  -- a call (`callCont`) from `t`
  have call : ∀ (t : State) rest rs fn ext vals, t.callers = [] → t.mem = s.mem →
      t.frame.func = s.frame.func → t.frame.regs = s.frame.regs →
      t.frame.slots = s.frame.slots → f.extern? fn = some ext →
      step B.toEnv P s = Opt.callCont B.toEnv P t rest rs ext vals →
      step E.toEnv P.bare s = Opt.callCont E.toEnv P.bare t rest rs ext vals →
      raiseAt? E P.bare s = extRaise E P.bare s.mem ext vals →
      raiseAt? B P s = extRaise B P s.mem ext vals →
      XFollows B P ⟨s, []⟩ r := by
    intro t rest rs fn ext vals htc htm htf htr hts hext e1 e2 e3 e4
    cases hpf : P.func? ext.name with
    | none =>
      have hx : extRaise E P.bare s.mem ext vals = extRaise B P s.mem ext vals := by
        unfold extRaise
        simp only [Program.bare_func?, hU.base _ hpf, hpf]
      have hEt : E.toEnv.extern ext.name = B.toEnv.extern ext.name := by
        simp only [XEnv.toEnv, hU.base _ hpf]
      apply same
      simp only [stepX, e3, e4, hx, e1, e2]
      simp only [Opt.callCont, hpf, Program.bare_func?, hEt]
    | some g =>
      have hra : raiseAt? B P s = none := by rw [e4]; unfold extRaise; simp only [hpf]
      obtain ⟨hgP, hgn⟩ := Program.func?_some hpf
      have hsig : g.sig = ext.sig := hU.decl f hf fn ext hext g hpf
      obtain ⟨hs, hEg, -⟩ := hU.prog g hgP
      have hEg' : E.extern ext.name = some hs := by rw [← hgn]; exact hEg
      have hx : ∀ o, hs vals t.mem = o → extRaise E P.bare s.mem ext vals =
          match o with
          | .unwound e m => some (e, m)
          | _ => none := by
        intro o ho
        rw [← htm]
        unfold extRaise
        simp only [Program.bare_func?, hEg', ho]
        cases o <;> rfl
      have hst : ∀ o, hs vals t.mem = o → (∀ e m, o ≠ .unwound e m) →
          r = liftStep ⟨s, []⟩ (match o with
            | .returned rvals mem' =>
              if rvals.map (·.ty) == AbiParam.tys ext.sig.returns then
                continueWith t rest rs rvals mem'
              else .stuck s!"extern %{ext.name} returned values of the wrong types"
            | .trapped c => .trapped c
            | .stuck m => .stuck m
            | .unwound _ _ => .stuck "callee unwound (Clif.run has no unwinding)"
            | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel") := by
        intro o ho hnu
        have hxo : extRaise E P.bare s.mem ext vals = none := by
          rw [hx o ho]; cases o <;> first | rfl | exact absurd rfl (hnu _ _)
        rw [← hr]
        simp only [stepX, e3, hxo, e2]
        simp only [Opt.callCont, Program.bare_func?, XEnv.toEnv, hEg', Option.map_some, ho]
        cases o <;> rfl
      refine atomic t rest rs g vals hgP htc htf htr hts hra
        (by rw [e1]; simp only [Opt.callCont, hpf, hsig, beq_self_eq_true, Bool.and_self,
          ↓reduceIte, htc]) hs hEg (fun rv m2 ho hty => ?_) (fun c ho => ?_) (fun e m ho => ?_)
        (fun ho => ?_)
      · rw [hst _ ho (fun _ _ h => by cases h)]
        simp only [hty, hsig, beq_self_eq_true, ↓reduceIte]
      · rw [hst _ ho (fun _ _ h => by cases h)]
        rfl
      · rw [← hr]
        simp only [stepX, e3, hx _ ho]
      · rcases ho with ⟨msg, ho⟩ | ho
        · exact ⟨msg, by rw [hst _ ho (fun _ _ h => by cases h)]; rfl⟩
        · exact ⟨_, by rw [hst _ ho (fun _ _ h => by cases h)]; rfl⟩
  -- an indirect call (`indCont`) from `t`
  have ind : ∀ (t : State) rest rs sig d a v, t.callers = [] → t.mem = s.mem →
      t.frame.func = s.frame.func → t.frame.regs = s.frame.regs →
      t.frame.slots = s.frame.slots → IndSig f d →
      step B.toEnv P s = indCont B.toEnv P t rest rs sig d a v →
      step E.toEnv P.bare s = indCont E.toEnv P.bare t rest rs sig d a v →
      raiseAt? E P.bare s = externAtRaise E P.bare t.mem d a v →
      raiseAt? B P s = (match P.funcs.find? fun g => (t.mem.symbols g.name) == some a with
        | some _ => none
        | none => externAtRaise B P t.mem d a v) →
      XFollows B P ⟨s, []⟩ r := by
    intro t rest rs sig d a v htc htm htf htr hts hdS e1 e2 e3 e4
    have hnf : ¬ IndFree f := hdS.not_indFree
    have hJ := hio hnf
    have hm : t.mem.symbols = syms := htm ▸ hI.syms hnf
    have hbare : ∀ E2 : Env, indCont E2 P.bare t rest rs sig d a v =
        StepResult.ofRes (callExternAt E2 P.bare t.mem d a v) fun (rv, m') =>
          continueWith t rest rs rv m' := fun _ => rfl
    cases hfind : P.funcs.find? (fun g => t.mem.symbols g.name == some a) with
    | none =>
      rw [hfind] at e4
      dsimp only at e4
      obtain ⟨hok, htr', hrs, hrs'⟩ := unlinkX_externAt (d := d) (v := v) hU hJ hm hfind
      cases hx : externAtRaise E P.bare t.mem d a v with
      | some em =>
        apply same
        simp only [stepX, e3, e4, hx, hrs em hx]
      | none =>
      have hbs : ∀ msg, callExternAt E.toEnv P.bare t.mem d a v = .stuck msg → False :=
        fun msg hc' => hns msg (by
          rw [← hr]
          simp only [stepX, e3, hx, e2, hbare, hc', StepResult.ofRes, liftStep])
      cases hxB : externAtRaise B P t.mem d a v with
      | some em =>
        rcases hrs' em hxB with h' | ⟨msg, h'⟩
        · rw [hx] at h'; cases h'
        · exact (hbs msg h').elim
      | none =>
        have hra : raiseAt? B P s = none := by rw [e4, hxB]
        have hw : indCont B.toEnv P t rest rs sig d a v =
            StepResult.ofRes (callExternAt B.toEnv P t.mem d a v) fun (rv, m') =>
              continueWith t rest rs rv m' := by
          simp only [indCont, hfind]
        cases hc' : callExternAt E.toEnv P.bare t.mem d a v with
        | ok q =>
          apply same
          simp only [stepX, e3, hx, hra, e1, e2, hbare, hw, hc', hok q hc']
        | trap c =>
          apply same
          simp only [stepX, e3, hx, hra, e1, e2, hbare, hw, hc', htr' c hc']
        | stuck msg => exact (hbs msg hc').elim
    | some h =>
      have hra : raiseAt? B P s = none := by rw [e4, hfind]
      have hhP := List.mem_of_find?_eq_some hfind
      have hha : t.mem.symbols h.name = some a := by simpa using List.find?_some hfind
      have hname : (E.names ++ P.bare.externNames).find?
          (fun n => t.mem.symbols n == some a) = some h.name := by
        obtain ⟨rest', hn, -⟩ := hU.names
        simp only [hn, Program.bare_externNames, List.append_nil, List.find?_append,
          List.find?_map, Function.comp_def, hfind, Option.map_some, Option.some_or]
      have hpf : P.func? h.name = some h := by
        cases e : P.func? h.name with
        | none => exact absurd rfl (Program.func?_none e h hhP)
        | some g =>
          obtain ⟨hg, hgn⟩ := Program.func?_some e
          rw [name_inj hU.nd hg hhP hgn]
      obtain ⟨hs, hEh, hprog⟩ := hU.prog h hhP
      have hsO : E.sigOf h.name = some h.sig := by rw [hU.sigOf, hpf]; rfl
      cases hsig : d.abiMatch h.sig with
      | false =>
        have hx : externAtRaise E P.bare t.mem d a v = none := by
          simp only [externAtRaise, hname, hEh, hsO, Option.all_some, hsig, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte]
        have : ∃ msg, r = .stuck msg := by
          refine ⟨s!"call_indirect: signature does not match %{h.name}", ?_⟩
          rw [← hr]
          simp only [stepX, e3, hx, e2, hbare]
          simp only [callExternAt, hname, Res.ofOption_some,
            Res.ok_bind, XEnv.toEnv, hEh, Option.map_some, hsO, Option.all_some, hsig]
          rfl
        obtain ⟨msg, hm'⟩ := this
        exact absurd hm' (hns msg)
      | true =>
        have hsig' := Signature.abiMatch_eq_true.mp hsig
        -- the arguments have the call site's types when `h` is entered
        have hvt : ∀ o, hs v t.mem = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
            v.map (·.ty) = AbiParam.tys d.params := by
          intro o ho h1 h2
          obtain ⟨fr', mem', he, -⟩ := hprog v t.mem o ho h1 h2
          obtain ⟨_, _, _, h1', -⟩ := Opt.enterFunc_ok he
          rw [h1', hsig'.1]
        have hx : ∀ o, hs v t.mem = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
            externAtRaise E P.bare t.mem d a v =
            match o with
            | .unwound e m => some (e, m)
            | _ => none := by
          intro o ho h1 h2
          simp only [externAtRaise, hname, hEh, hsO, Option.all_some, hsig, hvt o ho h1 h2,
            beq_self_eq_true, Bool.and_self, ↓reduceIte, ho]
          cases o <;> rfl
        refine atomic t rest rs h v hhP htc htf htr hts hra
          (by rw [e1]; simp only [indCont, hfind, hsig, ↓reduceIte, htc]) hs hEh
          (fun rv m2 ho hty => ?_) (fun c ho => ?_) (fun e m ho => ?_)
          (fun ho => ?_)
        · have h1 : ∀ msg, (XOutcome.returned rv m2) ≠ .stuck msg := fun _ h => by cases h
          have h2 : (XOutcome.returned rv m2) ≠ .outOfFuel := fun h => by cases h
          rw [← hr]
          simp only [stepX, e3, hx _ ho h1 h2, e2, hbare]
          simp only [callExternAt, hname, Res.ofOption_some, Res.ok_bind, XEnv.toEnv, hEh,
            Option.map_some, hsO, Option.all_some, hsig, checkTys, hvt _ ho h1 h2,
            beq_self_eq_true, Res.check_true, ho, XOutcome.toOutcome, hty, hsig'.2.2,
            ↓reduceIte, Res.pure_eq, StepResult.ofRes_ok]
        · have h1 : ∀ msg, (XOutcome.trapped c) ≠ .stuck msg := fun _ h => by cases h
          have h2 : (XOutcome.trapped c) ≠ .outOfFuel := fun h => by cases h
          rw [← hr]
          simp only [stepX, e3, hx _ ho h1 h2, e2, hbare]
          simp only [callExternAt, hname, Res.ofOption_some, Res.ok_bind, XEnv.toEnv, hEh,
            Option.map_some, hsO, Option.all_some, hsig, checkTys, hvt _ ho h1 h2,
            beq_self_eq_true, Res.check_true, ho, XOutcome.toOutcome, StepResult.ofRes_trap,
            liftStep]
        · have h1 : ∀ msg, (XOutcome.unwound e m) ≠ .stuck msg := fun _ h => by cases h
          have h2 : (XOutcome.unwound e m) ≠ .outOfFuel := fun h => by cases h
          rw [← hr]
          simp only [stepX, e3, hx _ ho h1 h2]
        · -- a stuck or unfinished callee: the per-function step is stuck
          have hxn : externAtRaise E P.bare t.mem d a v = none := by
            rcases ho with ⟨msg, ho⟩ | ho <;> simp only [externAtRaise, hname, hEh, ho] <;> simp
          have hok : ∀ q, callExternAt E.toEnv P.bare t.mem d a v ≠ .ok q := by
            intro q hq
            obtain ⟨n, g, h1, hg, -, -, rv, m', hgo, -⟩ := callExternAt_ok_iff.mp hq
            have h1' : (E.names ++ P.bare.externNames).find?
                (fun n => t.mem.symbols n == some a) = some n := h1
            rw [hname] at h1'
            cases h1'
            simp only [XEnv.toEnv, hEh, Option.map_some, Option.some.injEq] at hg
            subst hg
            rcases ho with ⟨msg, ho⟩ | ho <;> simp [ho, XOutcome.toOutcome] at hgo
          have htp : ∀ c, callExternAt E.toEnv P.bare t.mem d a v ≠ .trap c := by
            intro c hq
            obtain ⟨n, g, h1, hg, -, -, hgo⟩ := callExternAt_trap_iff.mp hq
            have h1' : (E.names ++ P.bare.externNames).find?
                (fun n => t.mem.symbols n == some a) = some n := h1
            rw [hname] at h1'
            cases h1'
            simp only [XEnv.toEnv, hEh, Option.map_some, Option.some.injEq] at hg
            subst hg
            rcases ho with ⟨msg, ho⟩ | ho <;> simp [ho, XOutcome.toOutcome] at hgo
          rw [← hr]
          simp only [stepX, e3, hxn, e2, hbare]
          cases hce : callExternAt E.toEnv P.bare t.mem d a v with
          | ok q => exact absurd hce (hok q)
          | trap c => exact absurd hce (htp c)
          | stuck msg => exact ⟨msg, rfl⟩
  -- the shapes of the step
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · -- a `try_call`
    have e1 := step_try B.toEnv P s hb ht
    have e2 := step_try E.toEnv P.bare s hb ht
    have r1 : raiseAt? B P s = tryCallRaise B P s.mem s.frame fn args et := by
      simp only [raiseAt?, hb, ht]
    have r2 : raiseAt? E P.bare s = tryCallRaise E P.bare s.mem s.frame fn args et := by
      simp only [raiseAt?, hb, ht]
    rw [tryCallRaise_eq] at r1 r2
    cases hpre : tryPre s.frame fn et with
    | trap c =>
      apply same
      simp only [stepX, r1, r2, hpre, e1, e2, StepResult.ofRes]
    | stuck m =>
      apply same
      simp only [stepX, r1, r2, hpre, e1, e2, StepResult.ofRes]
    | ok q =>
      obtain ⟨n, b, bc⟩ := q
      rw [hpre] at r1 r2 e1 e2
      simp only [StepResult.ofRes] at e1 e2
      rw [callRaise_eq] at r1 r2
      have hca := callArgs_tryState s bc fn args
      cases hc' : Opt.callArgs s.frame fn args with
      | trap c =>
        apply same
        simp only [stepX, r1, r2, hc', e1, e2, hca]
      | stuck m =>
        apply same
        simp only [stepX, r1, r2, hc', e1, e2, hca]
      | ok q =>
        obtain ⟨ext, vals⟩ := q
        rw [hc'] at r1 r2
        dsimp only at r1 r2
        rw [hca, hc'] at e1 e2
        simp only at e1 e2
        have hext : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hc'
        exact call (tryState s bc) [] _ fn ext vals hc rfl rfl rfl rfl hext e1 e2 r2 r1
  · -- a `try_call_indirect`
    have e1 := step_tryInd B.toEnv P s hb ht
    have e2 := step_tryInd E.toEnv P.bare s hb ht
    have r1 : raiseAt? B P s = tryCallIndRaise B P s.mem s.frame callee args et := by
      simp only [raiseAt?, hb, ht]
    have r2 : raiseAt? E P.bare s = tryCallIndRaise E P.bare s.mem s.frame callee args et := by
      simp only [raiseAt?, hb, ht]
    rw [tryCallIndRaise_eq] at r1 r2
    cases hpre : tryIndPre s.frame et with
    | trap c =>
      apply same
      simp only [stepX, r1, r2, hpre, e1, e2, StepResult.ofRes]
    | stuck m =>
      apply same
      simp only [stepX, r1, r2, hpre, e1, e2, StepResult.ofRes]
    | ok q =>
      obtain ⟨n, b, bc⟩ := q
      rw [hpre] at r1 r2 e1 e2
      simp only [StepResult.ofRes] at e1 e2
      rw [callIndRaise_eq] at r1 r2
      have hpi := indPre_tryState s bc et.sig callee args
      cases hc' : indPre s.frame et.sig callee args with
      | trap c =>
        apply same
        simp only [stepX, r1, r2, hc', e1, e2, hpi]
      | stuck m =>
        apply same
        simp only [stepX, r1, r2, hc', e1, e2, hpi]
      | ok q =>
        obtain ⟨d, a, v⟩ := q
        rw [hc'] at r1 r2
        dsimp only at r1 r2
        rw [hpi, hc'] at e1 e2
        simp only at e1 e2
        simp only [Program.bare_funcs, List.find?_nil] at r2
        have hdS : IndSig f d := by
          have hl := indPre_lookup hc'
          rcases hI.frame with ⟨-, ⟨b0, hb0, -, ht0⟩ | ⟨-, bc0, ht0⟩⟩
          · rw [hff] at hb0
            refine ⟨b0, hb0, .inr ⟨callee, args, et, ht0.symm.trans ht, ?_⟩⟩
            rw [← hff]; exact hl
          · rw [ht] at ht0; cases ht0
        exact ind (tryState s bc) [] _ et.sig d a v hc rfl rfl rfl rfl hdS e1 e2 r2 r1
  · -- a `call_indirect` statement
    have e1 := step_ind B.toEnv P s hb hi
    have e2 := step_ind E.toEnv P.bare s hb hi
    have r1 : raiseAt? B P s = callIndRaise B P s.mem s.frame sig callee args := by
      simp only [raiseAt?, hb, hi]
    have r2 : raiseAt? E P.bare s = callIndRaise E P.bare s.mem s.frame sig callee args := by
      simp only [raiseAt?, hb, hi]
    rw [callIndRaise_eq] at r1 r2
    cases hc' : indPre s.frame sig callee args with
    | trap c =>
      apply same
      simp only [stepX, r1, r2, hc', e1, e2, StepResult.ofRes]
    | stuck m =>
      apply same
      simp only [stepX, r1, r2, hc', e1, e2, StepResult.ofRes]
    | ok q =>
      obtain ⟨d, a, v⟩ := q
      rw [hc'] at r1 r2 e1 e2
      dsimp only at r1 r2
      simp only [StepResult.ofRes] at e1 e2
      simp only [Program.bare_funcs, List.find?_nil] at r2
      have hdS : IndSig f d := by
        have hl := indPre_lookup hc'
        rcases hI.frame with ⟨-, ⟨b0, hb0, hsuf, -⟩ | ⟨hnil, -⟩⟩
        · rw [hff] at hb0
          refine ⟨b0, hb0, .inl ⟨st, hsuf.subset (by rw [hb]; simp), sig, callee, args, hi, ?_⟩⟩
          rw [← hff]; exact hl
        · rw [hnil] at hb; cases hb
      exact ind s rest st.results sig d a v hc rfl rfl rfl rfl hdS e1 e2 r2 r1
  · have e1 := Opt.step_eq_lift B.toEnv P s hci
    have e2 := Opt.step_eq_lift E.toEnv P.bare s hci
    have hlocal : (∀ ext vals rs rest, Opt.lstep s.frame s.mem ≠ .call ext vals rs rest) →
        XFollows B P ⟨s, []⟩ r := by
      intro hnc
      have r2 : raiseAt? E P.bare s = none := raiseAt_none_of_lstep hP hIP hci hnc
      have r1 : raiseAt? B P s = none := raiseAt_none_of_lstep hP hIP hci hnc
      apply same
      simp only [stepX, r1, r2, e1, e2]
      cases hl' : Opt.lstep s.frame s.mem with
      | call ext vals rs rest => exact absurd hl' (hnc ext vals rs rest)
      | tail ext vals => exact absurd hl' (lstep_ne_tail hP hIP)
      | _ => rfl
    cases hl : Opt.lstep s.frame s.mem with
    | call ext vals rs rest =>
      obtain ⟨st, fn, args, hb, hi, -, hca⟩ := Opt.lstep_call_inv hl
      rw [hl] at e1 e2
      have r1 : raiseAt? B P s = extRaise B P s.mem ext vals := by
        simp only [raiseAt?, hb, hi, callRaise_eq, hca]
      have r2 : raiseAt? E P.bare s = extRaise E P.bare s.mem ext vals := by
        simp only [raiseAt?, hb, hi, callRaise_eq, hca]
      have hext : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hca
      exact call s rest rs fn ext vals hc rfl rfl rfl rfl hext e1 e2 r2 r1
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hIP)
    | _ => exact hlocal (fun _ _ _ _ h => by rw [hl] at h; cases h)

/-- The per-function invariant after a step that continues, given the whole program follows it. -/
theorem UInv.nextX {s : State} (hI : UInv P f syms s) {xs1 : XState}
    (h : stepX E P.bare ⟨s, []⟩ = .next xs1) (hW : ReachesX B P ⟨s, []⟩ xs1) :
    xs1 = ⟨xs1.s, []⟩ ∧ UInv P f syms xs1.s := by
  have hff : s.frame.func = f := by simpa [Program.only] using hI.frame.1
  have hIP : LFrame P s.frame := ⟨by rw [hff]; exact hf, hI.frame.2⟩
  obtain ⟨hcl, htr, hfr1⟩ := stepX_bare_next (hU.free f hf) hI.frame hI.callers h
  refine ⟨by rw [← htr], hcl, hfr1, fun hnf => ?_⟩
  have hXP : XInv P ⟨s, []⟩ :=
    ⟨⟨hIP, by rw [hI.callers]; exact fun _ h => nomatch h⟩, by simp [XState.Aligned, hI.callers]⟩
  rw [hW.symbols hU.free (hio hnf).scope.keep (hio hnf).scope.keepU hXP]
  exact hI.syms hnf

/-- **Unlinking runs with unwinding** (the converse of `runLoopX_linkR`): a per-function run of
`P.bare` under an environment that unlinks `P` that returns, traps or unwinds is a whole-program
run with the same outcome. -/
theorem unlinkX_run : ∀ (n : Nat) (s : State), UInv P f syms s → ∀ o,
    runLoopX E P.bare n ⟨s, []⟩ = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
      ∃ k, runLoopX B P k ⟨s, []⟩ = o := by
  intro n
  induction n with
  | zero => intro s _ o h _ hof; exact absurd (show o = .outOfFuel by rw [← h]; rfl) hof
  | succ n ih =>
    intro s hI o h hst hof
    rw [runLoopX_succ'] at h
    cases hr : stepX E P.bare ⟨s, []⟩ with
    | stuck msg => rw [hr] at h; exact absurd h.symm (hst msg)
    | next xs1 =>
      rw [hr] at h
      have hF := unlinkX_step hU hf hio hI hr (fun _ h => by cases h)
      obtain ⟨k, hk⟩ := hF.after
      obtain ⟨u, hu, hsu⟩ := hF
      have hW : ReachesX B P ⟨s, []⟩ xs1 := hu.snoc hsu
      obtain ⟨he, hI1⟩ := UInv.nextX hU hf hio hI hr hW
      rw [he] at h
      obtain ⟨k1, hk1⟩ := ih xs1.s hI1 o h hst hof
      refine ⟨k1 + 1 + k, ?_⟩
      rw [hk k1]
      show runLoopX B P k1 xs1 = o
      rw [he]; exact hk1
    | done v m =>
      rw [hr] at h
      obtain ⟨k, hk⟩ := (unlinkX_step hU hf hio hI hr (fun _ h => by cases h)).after
      exact ⟨0 + 1 + k, by rw [hk 0]; exact h⟩
    | unwound e m =>
      rw [hr] at h
      obtain ⟨k, hk⟩ := (unlinkX_step hU hf hio hI hr (fun _ h => by cases h)).after
      exact ⟨0 + 1 + k, by rw [hk 0]; exact h⟩
    | trapped c =>
      rw [hr] at h
      obtain ⟨k, hk⟩ := (unlinkX_step hU hf hio hI hr (fun _ h => by cases h)).after
      exact ⟨0 + 1 + k, by rw [hk 0]; exact h⟩

/-- **Reachability**: a state a per-function run with unwinding reaches is reached by the whole
program. -/
theorem unlinkX_reach : ∀ {xs xs' : XState}, ReachesX E P.bare xs xs' → ∀ s, xs = ⟨s, []⟩ →
    UInv P f syms s → ReachesX B P xs xs' := by
  intro xs xs' h
  induction h with
  | refl => exact fun _ _ _ => .refl _
  | @next xs xs1 xs2 hs _ ih =>
    intro s he hI
    subst he
    have hF := unlinkX_step hU hf hio hI hs (fun _ h => by cases h)
    obtain ⟨u, hu, hsu⟩ := hF
    have hW : ReachesX B P ⟨s, []⟩ xs1 := hu.snoc hsu
    obtain ⟨he1, hI1⟩ := UInv.nextX hU hf hio hI hs hW
    exact hW.trans (ih xs1.s he1 hI1)

end Step

end Clif
