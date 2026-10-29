module

public import FV.E2E.LinkClifN

@[expose] public section

/-!
# Unlinking: a per-function run is a whole-program run (S3)

`runLoop_linkN` (`LinkClifN.lean`) turns a complete whole-program run into a per-function run of
`P.bare` whose calls of `P`'s functions are atomic (the linked environment runs them). Here the
converse, for any environment `E` that **unlinks** `P` (`Unlink`: each function `h` of `P` is an
extern of `E` whose returns and traps are those of `h`'s whole-program run, every other extern
is `base`'s, `E` knows the signatures of `P`'s functions only): a per-function run of `P.bare`
under `E` that returns or traps is a whole-program run of `P` under `base` with the same outcome
(`unlink_run`), and every state it reaches is reached by the whole-program run (`unlink_reach`).

`unlink_step` classifies one per-function step: a step that is the whole program's (`StepSame`,
also under every environment agreeing with `E` outside `P`'s functions, `EnvAgree`), a call of a
function `h` of `P` (`StepCall`: the whole program enters `h`, the per-function step is
determined by `h`'s extern's outcome, `CallLike`), or a step stuck under every agreeing
environment. Indirect calls need `UnlinkInd` (the names `E` resolves addresses through are
`P`'s functions first, then names of `P` and `base`; `IndScope`; `base` knows no signature).
-/

namespace Clif

/-! ## Counted steps -/

/-- `k` whole steps from `s` to `s1`. -/
def StepsTo (env : Env) (p : Program) : Nat → State → State → Prop
  | 0, s, s1 => s1 = s
  | k + 1, s, s1 => ∃ s', step env p s = .next s' ∧ StepsTo env p k s' s1

theorem StepsTo.refl {env : Env} {p : Program} (s : State) : StepsTo env p 0 s s := rfl

theorem StepsTo.trans {env : Env} {p : Program} :
    ∀ {a b : Nat} {s s1 s2 : State}, StepsTo env p a s s1 → StepsTo env p b s1 s2 →
      StepsTo env p (a + b) s s2
  | 0, b, s, s1, s2, h1, h2 => by
    simp only [StepsTo] at h1
    subst h1
    simpa using h2
  | a + 1, b, s, s1, s2, ⟨s', hs, h1⟩, h2 => by
    rw [Nat.add_right_comm]
    exact ⟨s', hs, StepsTo.trans h1 h2⟩

theorem StepsTo.runLoop {env : Env} {p : Program} :
    ∀ {k : Nat} {s s1 : State}, StepsTo env p k s s1 →
      ∀ n, Clif.runLoop env p (n + k) s = Clif.runLoop env p n s1
  | 0, s, s1, h, n => by
    simp only [StepsTo] at h
    subst h
    rfl
  | k + 1, s, s1, ⟨s', hs, h⟩, n => by
    rw [← Nat.add_assoc, runLoop_succ', hs]
    exact StepsTo.runLoop h n

theorem StepsTo.below {env : Env} {p : Program} (K : List (Frame × List ValueId)) :
    ∀ {k : Nat} {s s1 : State}, StepsTo env p k s s1 → StepsTo env p k (s.below K) (s1.below K)
  | 0, s, s1, h => by
    simp only [StepsTo] at h ⊢
    rw [h]
  | k + 1, s, s1, ⟨s', hs, h⟩ => ⟨s'.below K, by rw [step_below, hs]; rfl, StepsTo.below K h⟩

/-- A run that returns reaches a state whose step finishes it. -/
theorem runLoop_returned_steps {env : Env} {p : Program} :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem),
      Clif.runLoop env p N s = .returned vals mem →
      ∃ k t, StepsTo env p k s t ∧ step env p t = .done vals mem
  | 0, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, h => by
    rw [runLoop_succ'] at h
    cases hs : step env p s with
    | next s1 =>
      rw [hs] at h
      obtain ⟨k, t, h1, h2⟩ := runLoop_returned_steps N s1 vals mem h
      exact ⟨k + 1, t, ⟨s1, hs, h1⟩, h2⟩
    | done v m =>
      rw [hs] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, s, rfl, hs⟩
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-- A run that traps reaches a state whose step traps. -/
theorem runLoop_trapped_steps {env : Env} {p : Program} :
    ∀ (N : Nat) (s : State) (c : TrapCode), Clif.runLoop env p N s = .trapped c →
      ∃ k t, StepsTo env p k s t ∧ step env p t = .trapped c
  | 0, _, _, h => by simp at h
  | N + 1, s, c, h => by
    rw [runLoop_succ'] at h
    cases hs : step env p s with
    | next s1 =>
      rw [hs] at h
      obtain ⟨k, t, h1, h2⟩ := runLoop_trapped_steps N s1 c h
      exact ⟨k + 1, t, ⟨s1, hs, h1⟩, h2⟩
    | done v m => rw [hs] at h; cases h
    | trapped c' =>
      rw [hs] at h
      simp only [afterStep, Outcome.trapped.injEq] at h
      subst h
      exact ⟨0, s, rfl, hs⟩
    | stuck m => rw [hs] at h; cases h

/-! ## Unlinking environments -/

/-- `E2` agrees with `E` on the names, the signatures and every extern that is no function of
`P`. -/
structure EnvAgree (P : Program) (E E2 : Env) : Prop where
  names : E2.names = E.names
  sigOf : E2.sigOf = E.sigOf
  base : ∀ n, P.func? n = none → E2.extern n = E.extern n

theorem EnvAgree.refl (P : Program) (E : Env) : EnvAgree P E E := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- **`E` unlinks `P` over `base`**: distinct names, no `return_call`, declarations of `P`'s
functions with their signatures, each function `h` of `P` an extern of `E` that returns or traps
only as `h`'s whole-program run does, every other extern `base`'s, and `E` knows exactly the
signatures of `P`'s functions. -/
structure Unlink (E : Env) (P : Program) (base : Env) : Prop where
  nd : (P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ P.funcs, LinkFree g
  decl : ∀ g ∈ P.funcs, ∀ fn e, g.extern? fn = some e → ∀ h, P.func? e.name = some h → h.sig = e.sig
  prog : ∀ h ∈ P.funcs, ∃ hs, E.extern h.name = some hs ∧ ∀ vals mem,
    (∀ rv m', hs vals mem = .returned rv m' → ∃ fr' mem', enterFunc h vals mem = .ok (fr', mem') ∧
      ∃ N, Clif.runLoop base P N ⟨fr', [], mem'⟩ = .returned rv m') ∧
    (∀ c, hs vals mem = .trapped c → ∃ fr' mem', enterFunc h vals mem = .ok (fr', mem') ∧
      ∃ N, Clif.runLoop base P N ⟨fr', [], mem'⟩ = .trapped c)
  base : ∀ n, P.func? n = none → E.extern n = base.extern n
  sigOf : ∀ n, E.sigOf n = (P.func? n).map (·.sig)

/-- For indirect calls: `E` resolves an address through `P`'s functions first, then names of `P`
and of `base`; `IndScope` (aliases are one extern of `base`); `base` knows no signature. -/
structure UnlinkInd (E : Env) (P : Program) (base : Env) (syms : String → Option Nat) : Prop where
  scope : IndScope P base syms
  baseSig : ∀ n, base.sigOf n = none
  names : ∃ rest, E.names = P.funcs.map (·.name) ++ rest ∧ ∀ n ∈ rest, n ∈ P.externNames ++ base.names

/-- A step that is the whole program's, under every environment agreeing with `E`. -/
def StepSame (E base : Env) (P : Program) (s : State) : Prop :=
  (∀ E2, EnvAgree P E E2 → step E2 P.bare s = step E P.bare s) ∧
  (∀ s1, step E P.bare s = .next s1 → step base P s = .next s1) ∧
  (∀ v m, step E P.bare s = .done v m → step base P s = .done v m) ∧
  (∀ c, step E P.bare s = .trapped c → step base P s = .trapped c)

/-- A per-function step `r` determined by the outcome `o` of an atomic call whose results (of the
types `rtys`) resume the callers `K`. -/
def CallLike (K : List (Frame × List ValueId)) (rtys : List Ty) (o : Outcome) (r : StepResult) :
    Prop :=
  (∀ rv m2, o = .returned rv m2 → rv.map (·.ty) = rtys → ∀ s1, resumeStep K rv m2 = .next s1 →
    r = .next s1) ∧
  (∀ c, o = .trapped c → r = .trapped c) ∧
  ((∃ msg, r = .stuck msg) ∨
    (∃ rv m2, o = .returned rv m2 ∧ rv.map (·.ty) = rtys ∧ r = resumeStep K rv m2) ∨
    (∃ c, o = .trapped c ∧ r = .trapped c))


/-- A step calling the function `h` of `P` on `vals`: the whole program enters `h` (the caller `c`
below), the per-function step is determined by `h`'s extern's outcome. -/
def StepCall (E base : Env) (P : Program) (s : State) : Prop :=
  ∃ h ∈ P.funcs, ∃ vals c, step base P s =
      StepResult.ofRes (enterFunc h vals s.mem)
        (fun (fr', mem') => .next ((⟨fr', [], mem'⟩ : State).below [c])) ∧
    ∀ E2, EnvAgree P E E2 → ∀ hs2, E2.extern h.name = some hs2 →
      CallLike [c] (AbiParam.tys h.sig.returns) (hs2 vals s.mem) (step E2 P.bare s)

/-- A step stuck under every environment agreeing with `E`. -/
def StepStuck (E : Env) (P : Program) (s : State) : Prop :=
  ∀ E2, EnvAgree P E E2 → ∃ msg, step E2 P.bare s = .stuck msg

/-- Binding a call's results in a frame without callers: the step resuming the frame, when that
continues, and otherwise stuck. -/
theorem continueWith_resume {t : State} (hc : t.callers = []) (rest : List Stmt)
    (rs : List ValueId) (rv : List Val) (m : Mem) :
    (∀ s1, resumeStep [({ t.frame with body := rest }, rs)] rv m = .next s1 →
      continueWith t rest rs rv m = .next s1) ∧
    ((∃ msg, continueWith t rest rs rv m = .stuck msg) ∨
      continueWith t rest rs rv m = resumeStep [({ t.frame with body := rest }, rs)] rv m) := by
  obtain ⟨fr, cs, mem⟩ := t
  simp only at hc
  subst hc
  cases h : fr.regs.setMany rs rv with
  | none =>
    simp only [continueWith, resumeStep, h]
    exact ⟨fun _ h => (nomatch h), .inl ⟨_, rfl⟩⟩
  | some regs =>
    constructor
    · intro s1 hs
      simp only [continueWith, resumeStep, h] at hs ⊢
      exact hs
    · right
      simp only [continueWith, resumeStep, h]

/-! ## Indirect calls of externs -/

/-- **A returning indirect call of an extern**: the first name with the callee address, its
extern, the signature and argument checks, the extern's return with the results' types. -/
theorem callExternAt_ok_iff {env : Env} {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} {r : List Val × Mem} :
    callExternAt env p mem d a vals = .ok r ↔
      ∃ n g, (env.names ++ p.externNames).find? (fun n => mem.symbols n == some a) = some n ∧
        env.extern n = some g ∧ (env.sigOf n).all d.abiMatch = true ∧
        vals.map (·.ty) = AbiParam.tys d.params ∧
        ∃ rv m', g vals mem = .returned rv m' ∧ rv.map (·.ty) = AbiParam.tys d.returns ∧
          r = (rv, m') := by
  constructor
  · intro h
    simp only [callExternAt, Opt.Res.bind_eq_ok, Opt.Res.ofOption_eq_ok, Opt.Res.check_eq_ok,
      checkTys, beq_iff_eq] at h
    obtain ⟨n, hn, g, hg, -, hs, -, hv, h⟩ := h
    refine ⟨n, g, hn, hg, hs, hv, ?_⟩
    revert h
    cases g vals mem with
    | returned rv m' =>
      intro h
      dsimp only at h
      split at h
      · rename_i hty
        simp only [Opt.Res.pure_eq_ok] at h
        exact ⟨rv, m', rfl, by simpa using hty, h.symm⟩
      · cases h
    | trapped c => intro h; cases h
    | stuck m => intro h; cases h
    | outOfFuel => intro h; cases h
  · rintro ⟨n, g, hn, hg, hs, hv, rv, m', ho, hrt, rfl⟩
    simp only [callExternAt, hn, hg, hs, checkTys, hv, beq_self_eq_true, Res.ofOption_some,
      Res.ok_bind, Res.check_true, ho, hrt, ite_true, Res.pure_eq]

/-- **A trapping indirect call of an extern**. -/
theorem callExternAt_trap_iff {env : Env} {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} {c : TrapCode} :
    callExternAt env p mem d a vals = .trap c ↔
      ∃ n g, (env.names ++ p.externNames).find? (fun n => mem.symbols n == some a) = some n ∧
        env.extern n = some g ∧ (env.sigOf n).all d.abiMatch = true ∧
        vals.map (·.ty) = AbiParam.tys d.params ∧ g vals mem = .trapped c := by
  constructor
  · intro h
    unfold callExternAt at h
    cases hn : (env.names ++ p.externNames).find? (fun n => mem.symbols n == some a) with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only [Res.ofOption_some, Res.ok_bind] at h
      cases hg : env.extern n with
      | none => rw [hg] at h; cases h
      | some g =>
        rw [hg] at h
        simp only [Res.ofOption_some, Res.ok_bind] at h
        cases hs : (env.sigOf n).all d.abiMatch with
        | false => rw [hs] at h; cases h
        | true =>
          rw [hs] at h
          simp only [Res.check_true, Res.ok_bind, checkTys] at h
          cases hv : (vals.map (·.ty) == AbiParam.tys d.params) with
          | false => rw [hv] at h; cases h
          | true =>
            rw [hv] at h
            simp only [Res.check_true, Res.ok_bind] at h
            refine ⟨n, g, rfl, hg, hs, by simpa using hv, ?_⟩
            revert h
            cases g vals mem with
            | returned rv m' =>
              intro h
              dsimp only at h
              split at h <;> cases h
            | trapped c' => intro h; cases h; rfl
            | stuck m => intro h; cases h
            | outOfFuel => intro h; cases h
  · rintro ⟨n, g, hn, hg, hs, hv, ho⟩
    simp only [callExternAt, hn, hg, hs, checkTys, hv, beq_self_eq_true, Res.ofOption_some,
      Res.ok_bind, Res.check_true, ho]

/-- The per-function and the whole-program call of an extern resolved at an address of no
function of `P`: the same outcome (aliases are one extern of `base`; neither knows a
signature). -/
theorem callExternAt_unlink {E : Env} {P : Program} {base : Env} {syms : String → Option Nat}
    (hU : Unlink E P base) (hI : UnlinkInd E P base syms) {mem : Mem} (hm : mem.symbols = syms)
    {d : Signature} {a : Nat} {vals : List Val}
    (hnone : P.funcs.find? (fun g => mem.symbols g.name == some a) = none) :
    (∀ r, callExternAt E P.bare mem d a vals = .ok r → callExternAt base P mem d a vals = .ok r) ∧
    (∀ c, callExternAt E P.bare mem d a vals = .trap c →
      callExternAt base P mem d a vals = .trap c) := by
  have hno : ∀ g ∈ P.funcs, mem.symbols g.name ≠ some a := fun g hg e => by
    have := List.find?_eq_none.mp hnone g hg
    simp [e] at this
  have hnp : ∀ n, mem.symbols n = some a → P.func? n = none := fun n hq => by
    cases e : P.func? n with
    | none => rfl
    | some g =>
      obtain ⟨hg, rfl⟩ := Program.func?_some e
      exact absurd hq (hno g hg)
  obtain ⟨rest, hn, hrest⟩ := hI.names
  -- the name the per-function call resolves: the whole program resolves a name of the same
  -- extern of `base`
  have hsame : ∀ n₁, (E.names ++ P.bare.externNames).find? (fun n => mem.symbols n == some a) =
      some n₁ → ∃ n₂, (base.names ++ P.externNames).find? (fun n => mem.symbols n == some a) =
        some n₂ ∧ E.extern n₁ = base.extern n₂ ∧ base.sigOf n₂ = none := by
    intro n₁ h₁
    have hq₁ : mem.symbols n₁ = some a := by simpa using List.find?_some h₁
    have hm₁ : n₁ ∈ E.names := by simpa using List.mem_of_find?_eq_some h₁
    have hp₁ := hnp n₁ hq₁
    have hr₁ : n₁ ∈ rest := by
      rw [hn] at hm₁
      rcases List.mem_append.mp hm₁ with h | h
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
        exact absurd hq₁ (hno g hg)
      · exact h
    have hb₁ : n₁ ∈ base.names ++ P.externNames := by
      rcases List.mem_append.mp (hrest n₁ hr₁) with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    cases h₂ : (base.names ++ P.externNames).find? (fun n => mem.symbols n == some a) with
    | none => exact absurd (List.find?_eq_none.mp h₂ n₁ hb₁) (by simp [hq₁])
    | some n₂ =>
      have hq₂ : mem.symbols n₂ = some a := by simpa using List.find?_some h₂
      have hm₂ := List.mem_of_find?_eq_some h₂
      have hp₂ := hnp n₂ hq₂
      have hn₁ : n₁ ∈ P.names ++ base.names := by
        rcases List.mem_append.mp (hrest n₁ hr₁) with h | h
        · exact List.mem_append_left _ (names_extern h)
        · exact List.mem_append_right _ h
      have hn₂ : n₂ ∈ P.names ++ base.names := by
        rcases List.mem_append.mp hm₂ with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (names_extern h)
      rw [hm] at hq₁ hq₂
      have hal := hI.scope.alias n₁ hn₁ n₂ hn₂ a hq₁ hq₂ hp₁ hp₂
      exact ⟨n₂, rfl, by rw [hU.base n₁ hp₁, hal], hI.baseSig n₂⟩
  refine ⟨fun r h => ?_, fun c h => ?_⟩
  · obtain ⟨n₁, g, h₁, hg, -, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp h
    obtain ⟨n₂, h₂, he, hs₂⟩ := hsame n₁ h₁
    exact callExternAt_ok_iff.mpr ⟨n₂, g, h₂, by rw [← he]; exact hg, by rw [hs₂]; rfl, hv,
      rv, m', ho, hrt, rfl⟩
  · obtain ⟨n₁, g, h₁, hg, -, hv, ho⟩ := callExternAt_trap_iff.mp h
    obtain ⟨n₂, h₂, he, hs₂⟩ := hsame n₁ h₁
    exact callExternAt_trap_iff.mpr ⟨n₂, g, h₂, by rw [← he]; exact hg, by rw [hs₂]; rfl, hv, ho⟩

/-! ## One step -/

theorem resumeStep_ne_done {c : Frame × List ValueId} {rv v : List Val} {m m' : Mem} :
    resumeStep [c] rv m ≠ .done v m' := by
  obtain ⟨c, rs⟩ := c
  simp only [resumeStep]
  split <;> intro h <;> cases h

theorem resumeStep_ne_trapped {c : Frame × List ValueId} {rv : List Val} {m : Mem}
    {t : TrapCode} : resumeStep [c] rv m ≠ .trapped t := by
  obtain ⟨c, rs⟩ := c
  simp only [resumeStep]
  split <;> intro h <;> cases h

/-- **One per-function step** (`StepSame`, `StepCall` or `StepStuck`) from a frame of `f` (no
callers). -/
theorem unlink_step {E base : Env} {P : Program} {syms : String → Option Nat}
    (hU : Unlink E P base) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms) {s : State} (hc : s.callers = [])
    (hI : LFrame (P.only f) s.frame) (hsy : ¬ IndFree f → s.mem.symbols = syms) :
    StepSame E base P s ∨ StepCall E base P s ∨ StepStuck E P s := by
  have hff : s.frame.func = f := by
    have := hI.1
    simpa [Program.only] using this
  have hIP : LFrame P s.frame := ⟨by rw [hff]; exact hf, hI.2⟩
  have same : (∀ E2, EnvAgree P E E2 → step E2 P.bare s = step base P s) →
      StepSame E base P s := by
    intro h
    have hE := h E (EnvAgree.refl P E)
    refine ⟨fun E2 hA => (h E2 hA).trans hE.symm, fun s1 h1 => ?_, fun v m h1 => ?_,
      fun c h1 => ?_⟩ <;> rw [← hE] <;> exact h1
  -- a call (`callCont`) of a declared extern from `t`
  have call : ∀ (t : State) rest rs fn ext vals, t.callers = [] → t.mem = s.mem →
      f.extern? fn = some ext →
      (∀ E2, EnvAgree P E E2 → step E2 P.bare s = Opt.callCont E2 P.bare t rest rs ext vals) →
      step base P s = Opt.callCont base P t rest rs ext vals →
      StepSame E base P s ∨ StepCall E base P s ∨ StepStuck E P s := by
    intro t rest rs fn ext vals htc htm hext e2 e1
    cases hpf : P.func? ext.name with
    | none =>
      refine .inl (same fun E2 hA => ?_)
      rw [e2 E2 hA, e1]
      simp only [Opt.callCont, Program.bare_func?, hpf, hA.base _ hpf, hU.base _ hpf]
    | some h =>
      obtain ⟨hhP, hhn⟩ := Program.func?_some hpf
      have hsig : h.sig = ext.sig := hU.decl f hf fn ext hext h hpf
      refine .inr (.inl ⟨h, hhP, vals, ({ t.frame with body := rest }, rs), ?_, ?_⟩)
      · rw [e1]
        simp only [Opt.callCont, hpf, hsig, beq_self_eq_true, Bool.and_self, ite_true, htc, htm]
        rfl
      · intro E2 hA hs2 he2
        rw [e2 E2 hA]
        simp only [Opt.callCont, Program.bare_func?, ← hhn, he2, htm, ← hsig]
        cases ho : hs2 vals s.mem with
        | returned rv m2 =>
          obtain ⟨hn, hcw⟩ := continueWith_resume htc rest rs rv m2
          refine ⟨fun rv' m2' he hty s1 hs1 => ?_, fun c he => (by cases he), ?_⟩
          · cases he
            simpa [hty] using hn s1 hs1
          · by_cases hty : rv.map (·.ty) = AbiParam.tys h.sig.returns
            · rcases hcw with ⟨msg, hm⟩ | hcw
              · exact .inl ⟨msg, by simp [hty, hm]⟩
              · exact .inr (.inl ⟨rv, m2, rfl, hty, by simp [hty, hcw]⟩)
            · exact .inl ⟨_, by simp [hty]; rfl⟩
        | trapped c =>
          exact ⟨fun _ _ he => (by cases he), fun c' he => (by cases he; rfl),
            .inr (.inr ⟨c, rfl, rfl⟩)⟩
        | stuck m =>
          exact ⟨fun _ _ he => (by cases he), fun _ he => (by cases he), .inl ⟨m, rfl⟩⟩
        | outOfFuel =>
          exact ⟨fun _ _ he => (by cases he), fun _ he => (by cases he), .inl ⟨_, rfl⟩⟩
  -- an indirect call (`indCont`) from `t`
  have ind : ∀ (t : State) rest rs sig d a v, t.callers = [] → t.mem = s.mem → ¬ IndFree f →
      (∀ E2, EnvAgree P E E2 → step E2 P.bare s = indCont E2 P.bare t rest rs sig d a v) →
      step base P s = indCont base P t rest rs sig d a v →
      StepSame E base P s ∨ StepCall E base P s ∨ StepStuck E P s := by
    intro t rest rs sig d a v htc htm hnf e2 e1
    have hJ := hio hnf
    have hm : t.mem.symbols = syms := htm ▸ hsy hnf
    obtain ⟨restN, hn, -⟩ := hJ.names
    have hbare : ∀ E2 : Env, indCont E2 P.bare t rest rs sig d a v =
        StepResult.ofRes (callExternAt E2 P.bare t.mem d a v) fun (rv, m') =>
          continueWith t rest rs rv m' := fun _ => rfl
    cases hfind : P.funcs.find? (fun g => t.mem.symbols g.name == some a) with
    | none =>
      have hcong : ∀ E2, EnvAgree P E E2 →
          callExternAt E2 P.bare t.mem d a v = callExternAt E P.bare t.mem d a v := by
        intro E2 hA
        refine callExternAt_congr hA.names (fun n hq => hA.base n ?_) fun n _ => by rw [hA.sigOf]
        cases e : P.func? n with
        | none => rfl
        | some g =>
          obtain ⟨hg, rfl⟩ := Program.func?_some e
          have := List.find?_eq_none.mp hfind g hg
          simp [hq] at this
      have hW : step base P s = StepResult.ofRes (callExternAt base P t.mem d a v) fun (rv, m') =>
          continueWith t rest rs rv m' := by
        rw [e1]
        simp only [indCont, hfind]
      have hE : step E P.bare s = StepResult.ofRes (callExternAt E P.bare t.mem d a v)
          fun (rv, m') => continueWith t rest rs rv m' := by
        rw [e2 E (EnvAgree.refl P E), hbare]
      obtain ⟨hok, htr⟩ := callExternAt_unlink hU hJ hm hfind (d := d) (vals := v)
      refine .inl ⟨fun E2 hA => by rw [e2 E2 hA, hbare, hcong E2 hA, hE], fun s1 h1 => ?_,
        fun v' m h1 => ?_, fun c h1 => ?_⟩
      · rw [hE] at h1
        rw [hW]
        cases hx : callExternAt E P.bare t.mem d a v with
        | ok r => rw [hok r hx]; rw [hx] at h1; exact h1
        | trap c => rw [hx] at h1; cases h1
        | stuck msg => rw [hx] at h1; cases h1
      · rw [hE] at h1
        cases hx : callExternAt E P.bare t.mem d a v with
        | ok r =>
          rw [hx] at h1
          obtain ⟨rv, m'⟩ := r
          simp only [StepResult.ofRes_ok, continueWith] at h1
          split at h1 <;> cases h1
        | trap c => rw [hx] at h1; cases h1
        | stuck msg => rw [hx] at h1; cases h1
      · rw [hE] at h1
        rw [hW]
        cases hx : callExternAt E P.bare t.mem d a v with
        | ok r =>
          rw [hx] at h1
          obtain ⟨rv, m'⟩ := r
          simp only [StepResult.ofRes_ok, continueWith] at h1
          split at h1 <;> cases h1
        | trap c' => rw [hx] at h1; rw [htr c' hx]; exact h1
        | stuck msg => rw [hx] at h1; cases h1
    | some h =>
      have hhP := List.mem_of_find?_eq_some hfind
      have hname : ∀ E2, EnvAgree P E E2 → (E2.names ++ P.bare.externNames).find?
          (fun n => t.mem.symbols n == some a) = some h.name := by
        intro E2 hA
        simp only [hA.names, hn, Program.bare_externNames, List.append_nil, List.find?_append,
          List.find?_map, Function.comp_def, hfind, Option.map_some, Option.some_or]
      have hpf : P.func? h.name = some h := by
        cases e : P.func? h.name with
        | none => exact absurd rfl (Program.func?_none e h hhP)
        | some g =>
          obtain ⟨hg, hgn⟩ := Program.func?_some e
          rw [name_inj hU.nd hg hhP hgn]
      have hsO : ∀ E2, EnvAgree P E E2 → E2.sigOf h.name = some h.sig := by
        intro E2 hA
        rw [hA.sigOf, hU.sigOf, hpf]
        rfl
      cases hsig : d.abiMatch h.sig with
      | false =>
        refine .inr (.inr fun E2 hA => ?_)
        rw [e2 E2 hA, hbare]
        cases hx : callExternAt E2 P.bare t.mem d a v with
        | ok r =>
          obtain ⟨n, g, h1, -, hs, -⟩ := callExternAt_ok_iff.mp hx
          rw [hname E2 hA] at h1
          cases h1
          rw [hsO E2 hA] at hs
          simp [hsig] at hs
        | trap c =>
          obtain ⟨n, g, h1, -, hs, -⟩ := callExternAt_trap_iff.mp hx
          rw [hname E2 hA] at h1
          cases h1
          rw [hsO E2 hA] at hs
          simp [hsig] at hs
        | stuck msg => exact ⟨msg, rfl⟩
      | true =>
        have hsig' := Signature.abiMatch_eq_true.mp hsig
        cases hvt : (v.map (·.ty) == AbiParam.tys d.params) with
        | false =>
          refine .inr (.inr fun E2 hA => ?_)
          rw [e2 E2 hA, hbare]
          cases hx : callExternAt E2 P.bare t.mem d a v with
          | ok r =>
            obtain ⟨-, -, -, -, -, hv, -⟩ := callExternAt_ok_iff.mp hx
            simp [hv] at hvt
          | trap c =>
            obtain ⟨-, -, -, -, -, hv, -⟩ := callExternAt_trap_iff.mp hx
            simp [hv] at hvt
          | stuck msg => exact ⟨msg, rfl⟩
        | true =>
          have hvt : v.map (·.ty) = AbiParam.tys d.params := by simpa using hvt
          refine .inr (.inl ⟨h, hhP, v, ({ t.frame with body := rest }, rs), ?_, ?_⟩)
          · rw [e1]
            simp only [indCont, hfind, hsig, ite_true, htc]
            rw [htm]
            rfl
          · intro E2 hA hs2 he2
            have hsA : (E2.sigOf h.name).all d.abiMatch = true := by
              rw [hsO E2 hA]; exact hsig
            have hnm := hname E2 hA
            rw [htm] at hnm
            rw [e2 E2 hA, hbare, htm]
            refine ⟨fun rv m2 ho hty s1 hs1 => ?_, fun c ho => ?_, ?_⟩
            · rw [callExternAt_ok_iff.mpr ⟨h.name, hs2, hnm, he2, hsA, hvt, rv, m2, ho,
                by rw [hty, hsig'.2.2], rfl⟩]
              simp only [StepResult.ofRes_ok]
              exact (continueWith_resume htc rest rs rv m2).1 s1 hs1
            · rw [callExternAt_trap_iff.mpr ⟨h.name, hs2, hnm, he2, hsA, hvt, ho⟩]
              rfl
            · cases hx : callExternAt E2 P.bare s.mem d a v with
              | ok r =>
                obtain ⟨n, g, h1, hg, -, -, rv, m2, ho, hrt, rfl⟩ := callExternAt_ok_iff.mp hx
                rw [hnm] at h1
                cases h1
                rw [he2] at hg
                cases hg
                rcases (continueWith_resume htc rest rs rv m2).2 with ⟨msg, hm⟩ | hcw
                · exact .inl ⟨msg, by simp only [StepResult.ofRes_ok]; exact hm⟩
                · exact .inr (.inl ⟨rv, m2, ho, by rw [hrt, hsig'.2.2], by
                    simp only [StepResult.ofRes_ok]; exact hcw⟩)
              | trap c =>
                obtain ⟨n, g, h1, hg, -, -, ho⟩ := callExternAt_trap_iff.mp hx
                rw [hnm] at h1
                cases h1
                rw [he2] at hg
                cases hg
                exact .inr (.inr ⟨c, ho, rfl⟩)
              | stuck msg => exact .inl ⟨msg, rfl⟩
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · -- a `try_call`
    have e1 := step_try base P s hb ht
    have e2 := fun E2 => step_try E2 P.bare s hb ht
    cases h1 : tryPre s.frame fn et with
    | trap c => exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; rfl)
    | stuck m => exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; rfl)
    | ok nbbc =>
    obtain ⟨n, b, bc⟩ := nbbc
    cases h2 : Opt.callArgs (tryState s bc).frame fn args with
    | trap c =>
      exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; simp only [StepResult.ofRes_ok, h2]; rfl)
    | stuck m =>
      exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; simp only [StepResult.ofRes_ok, h2]; rfl)
    | ok ev =>
    obtain ⟨ext, vals⟩ := ev
    have hext : f.extern? fn = some ext := by
      have := Opt.callArgs_extern h2; rw [← hff]; exact this
    exact call (tryState s bc) [] ((List.range n).map (b + ·)) fn ext vals hc rfl hext
      (fun E2 _ => by rw [e2 E2, h1]; simp only [StepResult.ofRes_ok, h2])
      (by rw [e1, h1]; simp only [StepResult.ofRes_ok, h2])
  · -- a `try_call_indirect`
    have e1 := step_tryInd base P s hb ht
    have e2 := fun E2 => step_tryInd E2 P.bare s hb ht
    have hnf : ¬ IndFree f := by
      intro hif
      rcases hI.2 with ⟨b0, hb0, -, ht0⟩ | ⟨-, bc0, ht0⟩
      · rw [hff] at hb0
        exact (hif b0 hb0).2 callee args et (ht0.symm.trans ht)
      · rw [ht] at ht0; cases ht0
    cases h1 : tryIndPre s.frame et with
    | trap c => exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; rfl)
    | stuck m => exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; rfl)
    | ok nbbc =>
    obtain ⟨n, b, bc⟩ := nbbc
    cases h2 : indPre (tryState s bc).frame et.sig callee args with
    | trap c =>
      exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; simp only [StepResult.ofRes_ok, h2]; rfl)
    | stuck m =>
      exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; simp only [StepResult.ofRes_ok, h2]; rfl)
    | ok dav =>
    obtain ⟨d, a, v⟩ := dav
    exact ind (tryState s bc) [] ((List.range n).map (b + ·)) et.sig d a v hc rfl hnf
      (fun E2 _ => by rw [e2 E2, h1]; simp only [StepResult.ofRes_ok, h2])
      (by rw [e1, h1]; simp only [StepResult.ofRes_ok, h2])
  · -- a `call_indirect` statement
    have e1 := step_ind base P s hb hi
    have e2 := fun E2 => step_ind E2 P.bare s hb hi
    have hnf : ¬ IndFree f := by
      intro hif
      rcases hI.2 with ⟨b0, hb0, hsuf, -⟩ | ⟨hnil, -⟩
      · rw [hff] at hb0
        exact (hif b0 hb0).1 st (hsuf.subset (by rw [hb]; simp)) sig callee args hi
      · rw [hnil] at hb; cases hb
    cases h1 : indPre s.frame sig callee args with
    | trap c => exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; rfl)
    | stuck m => exact .inl (same fun E2 _ => by rw [e2 E2, e1, h1]; rfl)
    | ok dav =>
    obtain ⟨d, a, v⟩ := dav
    exact ind s rest st.results sig d a v hc rfl hnf
      (fun E2 _ => by rw [e2 E2, h1]; rfl) (by rw [e1, h1]; rfl)
  · have e1 := Opt.step_eq_lift base P s hci
    have e2 := fun E2 => Opt.step_eq_lift E2 P.bare s hci
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 => exact .inl (same fun E2 _ => by rw [e2 E2, e1, hl]; rfl)
    | ret vals => exact .inl (same fun E2 _ => by rw [e2 E2, e1, hl]; rfl)
    | trap c => exact .inl (same fun E2 _ => by rw [e2 E2, e1, hl]; rfl)
    | stuck m => exact .inl (same fun E2 _ => by rw [e2 E2, e1, hl]; rfl)
    | tail ext vals => exact absurd hl (lstep_ne_tail hU.free hIP)
    | call ext vals rs rest =>
      obtain ⟨st, fn, args, hb, -, -, hca⟩ := Opt.lstep_call_inv hl
      have hext : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hca
      exact call s rest rs fn ext vals hc rfl hext (fun E2 _ => by rw [e2 E2, hl]; rfl)
        (by rw [e1, hl]; rfl)

/-! ## Runs -/

/-- `E` keeps the symbols when `base` does (its functions' returns are whole-program runs). -/
theorem Unlink.keeps {E base : Env} {P : Program} (hU : Unlink E P base)
    (hk : Opt.EnvKeepsSymbols base) : Opt.EnvKeepsSymbols E := by
  intro n gsem hg vals m rvals m' hr
  cases hpf : P.func? n with
  | none => rw [hU.base n hpf] at hg; exact hk n gsem hg vals m rvals m' hr
  | some h =>
    obtain ⟨hhP, rfl⟩ := Program.func?_some hpf
    obtain ⟨hs, he, hprog⟩ := hU.prog h hhP
    rw [he] at hg
    cases hg
    obtain ⟨fr', mem', hent, N, hrun⟩ := (hprog vals m).1 rvals m' hr
    have hI : LInv P ⟨fr', [], mem'⟩ := ⟨LFrame.enterFunc hhP hent, fun _ h => nomatch h⟩
    rw [runLoop_symbols hU.free hk N _ rvals m' hI hrun]
    exact enterFunc_symbols hent

/-- The per-function invariant: no callers, a frame of `f`, the symbols. -/
structure UInv (P : Program) (f : Function) (syms : String → Option Nat) (s : State) : Prop where
  callers : s.callers = []
  frame : LFrame (P.only f) s.frame
  syms : ¬ IndFree f → s.mem.symbols = syms

theorem UInv.next {E base : Env} {P : Program} {syms : String → Option Nat}
    (hU : Unlink E P base) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms)
    {s s1 : State} (hI : UInv P f syms s) (h : step E P.bare s = .next s1) : UInv P f syms s1 := by
  have hPf : ∀ g ∈ (P.only f).funcs, LinkFree g := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact hU.free g hf
  have hLI : LInv (P.only f) s := ⟨hI.frame, by rw [hI.callers]; exact fun _ h => nomatch h⟩
  have hff : s.frame.func = f := by
    have := hI.frame.1
    simpa [Program.only] using this
  have hIP : LFrame P s.frame := ⟨by rw [hff]; exact hf, hI.frame.2⟩
  refine ⟨step_bare_callers hU.free hIP hI.callers h,
    (step_next_linv hPf hLI h (fun _ h => nomatch h)).1.1, fun hn => ?_⟩
  rw [((step_symbols hPf (hU.keeps (hio hn).scope.keep) hLI).1 s1 h), hI.syms hn]

theorem UInv.steps {E base : Env} {P : Program} {syms : String → Option Nat}
    (hU : Unlink E P base) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms) :
    ∀ {k : Nat} {s s1 : State}, UInv P f syms s → StepsTo E P.bare k s s1 → UInv P f syms s1
  | 0, s, s1, hI, h => by simp only [StepsTo] at h; rw [h]; exact hI
  | k + 1, s, s1, hI, ⟨s', hs, h⟩ => UInv.steps hU hf hio (hI.next hU hf hio hs) h

/-- The whole program follows a per-function step that continues. -/
theorem unlink_next {E base : Env} {P : Program} {syms : String → Option Nat}
    (hU : Unlink E P base) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms) {s s1 : State} (hI : UInv P f syms s)
    (h : step E P.bare s = .next s1) : ∃ k, StepsTo base P k s s1 := by
  rcases unlink_step hU hf hio hI.callers hI.frame hI.syms with
    ⟨-, hn, -, -⟩ | ⟨g, hgP, vals, c, hW, hCL⟩ | hS
  · exact ⟨1, s1, hn s1 h, rfl⟩
  · obtain ⟨hs, he, hprog⟩ := hU.prog g hgP
    rcases (hCL E (EnvAgree.refl P E) hs he).2.2 with ⟨msg, hm⟩ | ⟨rv, m2, ho, -, hr⟩ | ⟨c', ho, hr⟩
    · rw [hm] at h; cases h
    · obtain ⟨fr', mem', hent, N, hrun⟩ := (hprog vals s.mem).1 rv m2 ho
      obtain ⟨j, t, hst, hdone⟩ := runLoop_returned_steps N _ rv m2 hrun
      rw [hent] at hW
      have h1 : StepsTo base P 1 s ((⟨fr', [], mem'⟩ : State).below [c]) := ⟨_, hW, rfl⟩
      have h3 : StepsTo base P 1 (t.below [c]) s1 := by
        refine ⟨s1, ?_, rfl⟩
        rw [step_below, hdone, ← h, hr]
        rfl
      exact ⟨1 + j + 1, (h1.trans (StepsTo.below [c] hst)).trans h3⟩
    · rw [hr] at h; cases h
  · obtain ⟨msg, hm⟩ := hS E (EnvAgree.refl P E)
    rw [hm] at h; cases h

/-- **Reachability**: a state a per-function run reaches is reached by the whole program. -/
theorem unlink_steps {E base : Env} {P : Program} {syms : String → Option Nat}
    (hU : Unlink E P base) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms) :
    ∀ {k : Nat} {s s1 : State}, UInv P f syms s → StepsTo E P.bare k s s1 →
      ∃ k', StepsTo base P k' s s1
  | 0, s, s1, _, h => ⟨0, h⟩
  | k + 1, s, s1, hI, ⟨s', hs, h⟩ => by
    obtain ⟨k1, h1⟩ := unlink_next hU hf hio hI hs
    obtain ⟨k2, h2⟩ := unlink_steps hU hf hio (hI.next hU hf hio hs) h
    exact ⟨k1 + k2, h1.trans h2⟩

/-- **Unlinking** (the converse of `runLoop_linkN`): a per-function run of `P.bare` under an
environment that unlinks `P` that returns or traps is a whole-program run with the same
outcome. -/
theorem unlink_run {E base : Env} {P : Program} {syms : String → Option Nat}
    (hU : Unlink E P base) {f : Function} (hf : f ∈ P.funcs)
    (hio : ¬ IndFree f → UnlinkInd E P base syms) {n : Nat} {s : State} (hI : UInv P f syms s) :
    (∀ v m, Clif.runLoop E P.bare n s = .returned v m → ∃ k, Clif.runLoop base P k s = .returned v m) ∧
    (∀ c, Clif.runLoop E P.bare n s = .trapped c → ∃ k, Clif.runLoop base P k s = .trapped c) := by
  refine ⟨fun v m h => ?_, fun c h => ?_⟩
  · obtain ⟨k, t, hst, hdone⟩ := runLoop_returned_steps n s v m h
    obtain ⟨k', hst'⟩ := unlink_steps hU hf hio hI hst
    have hIt := UInv.steps hU hf hio hI hst
    have hW : step base P t = .done v m := by
      rcases unlink_step hU hf hio hIt.callers hIt.frame hIt.syms with
        ⟨-, -, hd, -⟩ | ⟨g, hgP, vals, c, hW, hCL⟩ | hS
      · exact hd v m hdone
      · obtain ⟨hs, he, -⟩ := hU.prog g hgP
        rcases (hCL E (EnvAgree.refl P E) hs he).2.2 with ⟨msg, hm⟩ | ⟨rv, m2, -, -, hr⟩ |
          ⟨c', -, hr⟩
        · rw [hm] at hdone; cases hdone
        · rw [hr] at hdone; exact absurd hdone resumeStep_ne_done
        · rw [hr] at hdone; cases hdone
      · obtain ⟨msg, hm⟩ := hS E (EnvAgree.refl P E)
        rw [hm] at hdone; cases hdone
    refine ⟨1 + k', ?_⟩
    rw [hst'.runLoop 1, runLoop_succ', hW]
    rfl
  · obtain ⟨k, t, hst, htr⟩ := runLoop_trapped_steps n s c h
    obtain ⟨k', hst'⟩ := unlink_steps hU hf hio hI hst
    have hIt := UInv.steps hU hf hio hI hst
    have hW : ∃ j u, StepsTo base P j t u ∧ step base P u = .trapped c := by
      rcases unlink_step hU hf hio hIt.callers hIt.frame hIt.syms with
        ⟨-, -, -, ht⟩ | ⟨g, hgP, vals, c0, hW, hCL⟩ | hS
      · exact ⟨0, t, rfl, ht c htr⟩
      · obtain ⟨hs, he, hprog⟩ := hU.prog g hgP
        rcases (hCL E (EnvAgree.refl P E) hs he).2.2 with ⟨msg, hm⟩ | ⟨rv, m2, -, -, hr⟩ |
          ⟨c', ho, hr⟩
        · rw [hm] at htr; cases htr
        · rw [hr] at htr; exact absurd htr resumeStep_ne_trapped
        · rw [hr] at htr
          cases htr
          obtain ⟨fr', mem', hent, N, hrun⟩ := (hprog vals t.mem).2 c ho
          obtain ⟨j, u, hst2, htr2⟩ := runLoop_trapped_steps N _ c hrun
          rw [hent] at hW
          refine ⟨1 + j, u.below [c0], (show StepsTo base P 1 t _ from ⟨_, hW, rfl⟩).trans
            (StepsTo.below [c0] hst2), ?_⟩
          rw [step_below, htr2]
          rfl
      · obtain ⟨msg, hm⟩ := hS E (EnvAgree.refl P E)
        rw [hm] at htr; cases htr
    obtain ⟨j, u, hju, hu⟩ := hW
    refine ⟨1 + (k' + j), ?_⟩
    rw [(hst'.trans hju).runLoop 1, runLoop_succ', hu]
    rfl

end Clif
