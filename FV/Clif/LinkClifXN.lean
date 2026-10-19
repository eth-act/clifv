import FV.Clif.LinkClifX
import FV.E2E.LinkClifN

/-!
# Linking at the CLIF level with unwinding and bounded callee runs (S10f, #233)

`FV/E2E/LinkClifN.lean`'s counterpart for the runs with unwinding: `linkEnvRX P env R` runs a
called function `g` of `P` by `R` from its entry state (its `unwound` outcome is the extern's
exceptional result, raised at the call); `runLoopX_linkR`: a complete whole-program run with
unwinding of at most `F + 1` steps is a complete run of the program without functions
(`P.bare`) whose calls of the program's functions are atomic, when `R` is the callee's
whole-program run for every callee entered on the way — with `call_indirect`/
`try_call_indirect` (`IndScopeX`) and under restrictions `E` of the linked environment, as
`runLoop_linkR`. Instances: `runLoopX_linkN` (callees `M` steps), `runLoopX_linkD` (bounded
depth).
-/

namespace Clif

/-! ## The linked environment with callee runs `R` -/

/-- **The environment of the per-function programs of `P` with unwinding and the callee runs
`R`** (`linkEnvR`'s counterpart). -/
def linkEnvRX (P : Program) (env : XEnv) (R : State → XOutcome) : XEnv where
  extern n := match P.func? n with
    | some _ => some fun vals mem =>
      match initState P n vals mem with
      | .ok s => R s
      | .trap c => .trapped c
      | .stuck m => .stuck m
    | none => env.extern n
  names := P.names ++ env.names
  sigOf n := (P.func? n).map (·.sig)

section
variable {P : Program} {env : XEnv} {R : State → XOutcome}

theorem linkEnvRX_none {n : String} (h : P.func? n = none) :
    (linkEnvRX P env R).extern n = env.extern n := by
  simp [linkEnvRX, h]

theorem linkEnvRX_some {n : String} {g : Function} (h : P.func? n = some g) :
    (linkEnvRX P env R).extern n = some fun vals mem =>
      match initState P n vals mem with
      | .ok s => R s
      | .trap c => .trapped c
      | .stuck m => .stuck m := by
  simp [linkEnvRX, h]

/-- Without unwinding, `linkEnvRX` is `linkEnvR` with the callee runs read as `Clif.run`'s. -/
theorem linkEnvRX_toEnv :
    (linkEnvRX P env R).toEnv = linkEnvR P env.toEnv (fun s => (R s).toOutcome) := by
  simp only [XEnv.toEnv, linkEnvRX, linkEnvR, Env.mk.injEq, and_true]
  funext n
  cases P.func? n with
  | none => rfl
  | some g =>
    simp only [Option.map_some, Option.some.injEq]
    funext vals mem
    cases initState P n vals mem <;> rfl

end

/-! ## The scope of indirect calls, the symbols -/

/-- `IndScope` for an environment with unwinding: its externs keep the symbols, also when they
unwind. -/
structure IndScopeX (P : Program) (env : XEnv) (syms : String → Option Nat) : Prop where
  keep : Opt.EnvKeepsSymbols env.toEnv
  keepU : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
    m'.symbols = m.symbols
  inj : SymInj (P.funcs.map (·.name)) syms
  alias : ∀ a ∈ P.names ++ env.names, ∀ b ∈ P.names ++ env.names, ∀ x, syms a = some x →
    syms b = some x → P.func? a = none → P.func? b = none → env.extern a = env.extern b

theorem IndScopeX.toScope {P : Program} {env : XEnv} {syms : String → Option Nat}
    (h : IndScopeX P env syms) : IndScope P env.toEnv syms :=
  ⟨h.keep, h.inj, fun a ha b hb x h1 h2 h3 h4 => by
    simp only [XEnv.toEnv] at ha hb ⊢
    rw [h.alias a ha b hb x h1 h2 h3 h4]⟩

/-- A raising step's exception and memory are an extern's unwound outcome on the state's
memory. -/
theorem raiseAt_extern {env : XEnv} {p : Program} {s : State} {e : Exn} {m : Mem}
    (hr : raiseAt? env p s = some (e, m)) :
    ∃ n g vals, env.extern n = some g ∧ g vals s.mem = .unwound e m := by
  have hx : ∀ n g vals, env.extern n = some g →
      (match g vals s.mem with
        | .unwound e m => some (e, m)
        | _ => none : Option (Exn × Mem)) = some (e, m) →
      ∃ n g vals, env.extern n = some g ∧ g vals s.mem = .unwound e m := by
    intro n g vals hg h
    cases hu : g vals s.mem with
    | unwound e' m' =>
      rw [hu] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨n, g, vals, hg, hu⟩
    | _ => rw [hu] at h; cases h
  have hext : ∀ ext vals, extRaise env p s.mem ext vals = some (e, m) →
      ∃ n g vals, env.extern n = some g ∧ g vals s.mem = .unwound e m := by
    intro ext vals h
    unfold extRaise at h
    cases hp : p.func? ext.name with
    | some _ => rw [hp] at h; cases h
    | none =>
      rw [hp] at h
      cases hg : env.extern ext.name with
      | none => rw [hg] at h; cases h
      | some g => rw [hg] at h; exact hx _ g vals hg h
  have hcall : ∀ fr fn args, callRaise env p s.mem fr fn args = some (e, m) →
      ∃ n g vals, env.extern n = some g ∧ g vals s.mem = .unwound e m := by
    intro fr fn args h
    rw [callRaise_eq] at h
    split at h
    · exact hext _ _ h
    · cases h
  have hind : ∀ fr sig callee args, callIndRaise env p s.mem fr sig callee args = some (e, m) →
      ∃ n g vals, env.extern n = some g ∧ g vals s.mem = .unwound e m := by
    intro fr sig callee args h
    unfold callIndRaise at h
    split at h
    · split at h
      · cases h
      · unfold externAtRaise at h
        split at h
        · rename_i name _
          cases hg : env.extern name with
          | none => rw [hg] at h; cases h
          | some g =>
            rw [hg] at h
            dsimp only at h
            split at h
            · exact hx _ g _ hg h
            · cases h
        · cases h
    · cases h
  unfold raiseAt? at hr
  split at hr
  · split at hr
    · exact hcall _ _ _ hr
    · exact hind _ _ _ _ hr
    · cases hr
  · split at hr
    · unfold returnCallRaise at hr
      split at hr
      · split at hr
        · cases hr
        · split at hr
          · rename_i g hg
            exact hx _ g _ hg hr
          · cases hr
      · cases hr
    · rw [tryCallRaise_eq] at hr
      split at hr
      · exact hcall _ _ _ hr
      · cases hr
    · unfold tryCallIndRaise at hr
      split at hr
      · exact hind _ _ _ _ hr
      · cases hr
    · cases hr

theorem unwindFrom_symbols (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (xs' : XState), unwindFrom e fr cs ts mem = .next xs' → xs'.s.mem.symbols = mem.symbols
  | fr, [], _, mem, xs', h => by simp [unwindFrom] at h
  | fr, (c, rs) :: cs, t :: ts, mem, xs', h => by
    simp only [unwindFrom] at h
    split at h
    · rename_i r _
      cases r with
      | ok fr' =>
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        simp only [Mem.leave_symbols]; rfl
      | _ => simp [XStepResult.ofRes] at h
    · rw [unwindFrom_symbols e c cs ts _ xs' h, Mem.leave_symbols]; rfl
  | fr, _ :: _, [], mem, xs', h => by simp [unwindFrom] at h

theorem resumeUnwind_symbols (e : Exn) :
    ∀ (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (xs' : XState), resumeUnwind e cs ts mem = .next xs' → xs'.s.mem.symbols = mem.symbols
  | [], _, mem, xs', h => by simp [resumeUnwind] at h
  | (c, rs) :: cs, t :: ts, mem, xs', h => by
    simp only [resumeUnwind] at h
    split at h
    · rename_i r _
      cases r with
      | ok fr' =>
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h; rfl
      | _ => simp [XStepResult.ofRes] at h
    · exact unwindFrom_symbols e c cs ts _ xs' h
  | _ :: _, [], mem, xs', h => by simp [resumeUnwind] at h

theorem raiseIn_symbols {xs xs' : XState} {e : Exn} {mem : Mem} (h : raiseIn xs e mem = .next xs') :
    xs'.s.mem.symbols = mem.symbols := by
  unfold raiseIn at h
  split at h
  · rename_i r _
    cases r with
    | ok fr' =>
      simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
      subst h; rfl
    | _ => simp [XStepResult.ofRes] at h
  · exact unwindFrom_symbols e _ _ _ _ xs' h

/-- A whole-program step with unwinding keeps the symbols when the externs do (also when they
unwind). -/
theorem stepX_symbols {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : Opt.EnvKeepsSymbols env.toEnv)
    (hkU : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
      m'.symbols = m.symbols)
    {xs xs' : XState} (hI : XInv P xs) (h : stepX env p xs = .next xs') :
    xs'.s.mem.symbols = xs.s.mem.symbols := by
  unfold stepX at h
  split at h
  · rename_i e mem hr
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hr
    rw [raiseIn_symbols h, hkU n g hg vals _ e mem hu]
  · cases hs : step env.toEnv p xs.s with
    | next s1 =>
      rw [hs] at h
      simp only [liftStep, XStepResult.next.injEq] at h
      subst h
      exact (step_symbols hP hk hI.1).1 s1 hs
    | _ => rw [hs] at h; simp [liftStep] at h

/-! ## Reachable states of runs with unwinding -/

/-- `xs'` is reachable from `xs` by whole-program steps with unwinding that continue. -/
inductive ReachesX (env : XEnv) (p : Program) : XState → XState → Prop
  | refl (xs : XState) : ReachesX env p xs xs
  | next {xs xs' xs'' : XState} : stepX env p xs = .next xs' → ReachesX env p xs' xs'' →
      ReachesX env p xs xs''

theorem ReachesX.snoc {env : XEnv} {p : Program} {xs xs' xs'' : XState}
    (h : ReachesX env p xs xs') (h' : stepX env p xs' = .next xs'') : ReachesX env p xs xs'' := by
  induction h with
  | refl => exact .next h' (.refl _)
  | next hs _ ih => exact .next hs (ih h')

theorem ReachesX.trans {env : XEnv} {p : Program} {xs xs' xs'' : XState}
    (h : ReachesX env p xs xs') (h' : ReachesX env p xs' xs'') : ReachesX env p xs xs'' := by
  induction h with
  | refl => exact h'
  | next hs _ ih => exact .next hs (ih h')

theorem ReachesX.xinv {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs u : XState} (h : ReachesX env P xs u) (hI : XInv P xs) : XInv P u := by
  induction h with
  | refl => exact hI
  | next hs _ ih => exact ih (stepX_next_xinv hP hI hs)

/-- With callers `K` (tables `T`) below the stack the same states are reachable. -/
theorem ReachesX.under {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs u : XState} (K : List (Frame × List ValueId)) (T : List (Option ExnTable))
    (h : ReachesX env P xs u) (hI : XInv P xs) : ReachesX env P (xs.below K T) (u.below K T) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih =>
    refine .next (by rw [stepX_below hP hI, hs]; rfl) (ih (stepX_next_xinv hP hI hs))

theorem ReachesX.symbols {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : Opt.EnvKeepsSymbols env.toEnv)
    (hkU : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
      m'.symbols = m.symbols)
    {xs u : XState} (h : ReachesX env P xs u) (hI : XInv P xs) :
    u.s.mem.symbols = xs.s.mem.symbols := by
  induction h with
  | refl => rfl
  | next hs _ ih =>
    rw [ih (stepX_next_xinv hP hI hs), stepX_symbols hP hk hkU hI hs]

theorem runLoopX_returned_reaches (env : XEnv) (p : Program) :
    ∀ (N : Nat) (xs : XState) (vals : List Val) (mem : Mem),
      runLoopX env p N xs = .returned vals mem →
      ∃ u, ReachesX env p xs u ∧ stepX env p u = .done vals mem
  | 0, _, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, vals, mem, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env p xs with
    | next xs1 =>
      rw [hs] at h
      obtain ⟨u, hu, hd⟩ := runLoopX_returned_reaches env p N xs1 vals mem h
      exact ⟨u, .next hs hu, hd⟩
    | done v m =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨xs, .refl _, hs⟩
    | _ => rw [hs] at h; cases h

theorem runLoopX_unwound_reaches (env : XEnv) (p : Program) :
    ∀ (N : Nat) (xs : XState) (e : Exn) (mem : Mem),
      runLoopX env p N xs = .unwound e mem →
      ∃ u, ReachesX env p xs u ∧ stepX env p u = .unwound e mem
  | 0, _, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, e, mem, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env p xs with
    | next xs1 =>
      rw [hs] at h
      obtain ⟨u, hu, hd⟩ := runLoopX_unwound_reaches env p N xs1 e mem h
      exact ⟨u, .next hs hu, hd⟩
    | unwound e' m =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨xs, .refl _, hs⟩
    | _ => rw [hs] at h; cases h

/-- A whole-program run of call depth at most `d` from `xs`: every state it reaches has at most
`d` callers. -/
def DepthLeX (env : XEnv) (p : Program) (d : Nat) (xs : XState) : Prop :=
  ∀ u, ReachesX env p xs u → u.s.callers.length ≤ d

/-- Within a run of call depth at most `d`, the run of a callee entered with the callers `K`
below has call depth at most `d - 1`. -/
theorem DepthLeX.callee {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv} {d : Nat}
    {xs : XState} {t0 : XState} {K : List (Frame × List ValueId)} {T : List (Option ExnTable)}
    (hK : K ≠ []) (hI : XInv P t0) (hd : DepthLeX env P d xs)
    (hr : ReachesX env P xs (t0.below K T)) : 0 < d ∧ DepthLeX env P (d - 1) t0 := by
  have hk : 0 < K.length := List.length_pos_iff.mpr hK
  have h0 := hd _ hr
  simp only [XState.below, State.below_callers, List.length_append] at h0
  refine ⟨by omega, fun u hu => ?_⟩
  have := hd _ (hr.trans (hu.under hP K T hI))
  simp only [XState.below, State.below_callers, List.length_append] at this
  omega

/-! ## Raising calls in the program without functions -/

@[simp] theorem linkEnvRX_names {P : Program} {env : XEnv} {R : State → XOutcome} :
    (linkEnvRX P env R).names = P.names ++ env.names := rfl

@[simp] theorem linkEnvRX_sigOf {P : Program} {env : XEnv} {R : State → XOutcome} {n : String} :
    (linkEnvRX P env R).sigOf n = (P.func? n).map (·.sig) := rfl

/-- `externAtRaise` resolving the callee address to names with the same extern, the first one's
signature unknown: the same raise, unless the second's signature check fails (then the second's
`callExternAt` is stuck). -/
theorem externAtRaise_alias {E₁ E₂ : XEnv} {p₁ p₂ : Program} {mem : Mem} {d : Signature}
    {a : Nat} {vals : List Val} {n₁ n₂ : String}
    (h₁ : (E₁.names ++ p₁.externNames).find? (fun n => mem.symbols n == some a) = some n₁)
    (h₂ : (E₂.names ++ p₂.externNames).find? (fun n => mem.symbols n == some a) = some n₂)
    (he : E₁.extern n₁ = E₂.extern n₂) (hs : E₁.sigOf n₁ = none) :
    externAtRaise E₁ p₁ mem d a vals = externAtRaise E₂ p₂ mem d a vals ∨
      (externAtRaise E₂ p₂ mem d a vals = none ∧
        ∃ m, callExternAt E₂.toEnv p₂ mem d a vals = .stuck m) := by
  have h₂' : (E₂.toEnv.names ++ p₂.externNames).find? (fun n => mem.symbols n == some a) =
      some n₂ := h₂
  unfold externAtRaise
  rw [h₁, h₂]
  dsimp only
  rw [he, hs]
  cases hg : E₂.extern n₂ with
  | none => exact .inl rfl
  | some g =>
    simp only [Option.all_none, Bool.true_and]
    cases hc : (E₂.sigOf n₂).all d.abiMatch with
    | true => exact .inl (by simp)
    | false =>
      refine .inr ⟨by simp, ?_⟩
      simp only [callExternAt, XEnv.toEnv]
      rw [h₂]
      simp only [Res.ofOption_some, Res.ok_bind, hg, Option.map_some, hc]
      exact ⟨_, rfl⟩

/-- `externAtRaise` under environments with the same names and the same externs and signatures
at the names with the callee address. -/
theorem externAtRaise_congr {E₁ E₂ : XEnv} {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} (hn : E₁.names = E₂.names)
    (hx : ∀ n, mem.symbols n = some a → E₁.extern n = E₂.extern n)
    (hs : ∀ n, mem.symbols n = some a → E₁.sigOf n = E₂.sigOf n) :
    externAtRaise E₁ p mem d a vals = externAtRaise E₂ p mem d a vals := by
  unfold externAtRaise
  rw [hn]
  cases hf : (E₂.names ++ p.externNames).find? (fun n => mem.symbols n == some a) with
  | none => rfl
  | some n =>
    have hq : mem.symbols n = some a := by simpa using List.find?_some hf
    simp only [hx n hq, hs n hq]

theorem func?_none_of_find {P : Program} {mem : Mem} {a : Nat}
    (hnone : P.funcs.find? (fun g => mem.symbols g.name == some a) = none) {n : String}
    (hq : mem.symbols n = some a) : P.func? n = none := by
  cases e : P.func? n with
  | none => rfl
  | some g =>
    obtain ⟨hg, rfl⟩ := Program.func?_some e
    have := List.find?_eq_none.mp hnone g hg
    simp [hq] at this

/-- An indirect call to no function of `P` raises, in the program without functions, as in the
whole program (`IndScopeX.alias`), unless the whole program's call is stuck. -/
theorem externAtRaise_eq {P : Program} {env : XEnv} {syms : String → Option Nat}
    {R : State → XOutcome} (hS : IndScopeX P env syms) {mem : Mem} (hm : mem.symbols = syms)
    {d : Signature} {a : Nat} {vals : List Val}
    (hnone : P.funcs.find? (fun g => mem.symbols g.name == some a) = none) :
    externAtRaise (linkEnvRX P env R) P.bare mem d a vals = externAtRaise env P mem d a vals ∨
      (externAtRaise env P mem d a vals = none ∧
        ∃ m, callExternAt env.toEnv P mem d a vals = .stuck m) := by
  have hno : ∀ g ∈ P.funcs, mem.symbols g.name ≠ some a := fun g hg e => by
    have := List.find?_eq_none.mp hnone g hg
    simp [e] at this
  have hiff : ∀ n, n ∈ (linkEnvRX P env R).names ++ P.bare.externNames ↔
      n ∈ P.names ++ env.names := fun n => by
    rw [Program.bare_externNames, List.append_nil, linkEnvRX_names]
  have hsub : ∀ n, mem.symbols n = some a →
      n ∈ (linkEnvRX P env R).names ++ P.bare.externNames → n ∈ env.names ++ P.externNames :=
    fun n hq hn => by
      rcases List.mem_append.mp ((hiff n).mp hn) with hn | hn
      · rcases List.mem_append.mp hn with hn | hn
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
          exact absurd hq (hno g hg)
        · exact List.mem_append_right _ hn
      · exact List.mem_append_left _ hn
  have hsup : ∀ n, n ∈ env.names ++ P.externNames →
      n ∈ (linkEnvRX P env R).names ++ P.bare.externNames := fun n hn => by
    refine (hiff n).mpr ?_
    rcases List.mem_append.mp hn with hn | hn
    · exact List.mem_append_right _ hn
    · exact List.mem_append_left _ (names_extern hn)
  cases h₂ : (env.names ++ P.externNames).find? (fun n => mem.symbols n == some a) with
  | none =>
    have h₁ : ((linkEnvRX P env R).names ++ P.bare.externNames).find?
        (fun n => mem.symbols n == some a) = none := by
      rw [List.find?_eq_none] at h₂ ⊢
      intro n hn hq
      exact h₂ n (hsub n (by simpa using hq) hn) hq
    left
    unfold externAtRaise
    rw [h₁, h₂]
  | some n₂ =>
    have hq₂ : mem.symbols n₂ = some a := by simpa using List.find?_some h₂
    have hm₂ := List.mem_of_find?_eq_some h₂
    cases h₁ : ((linkEnvRX P env R).names ++ P.bare.externNames).find?
        (fun n => mem.symbols n == some a) with
    | none => exact absurd (List.find?_eq_none.mp h₁ n₂ (hsup n₂ hm₂)) (by simp [hq₂])
    | some n₁ =>
      have hq₁ : mem.symbols n₁ = some a := by simpa using List.find?_some h₁
      have hm₁ := List.mem_of_find?_eq_some h₁
      have hp₁ := func?_none_of_find hnone hq₁
      have hp₂ := func?_none_of_find hnone hq₂
      refine externAtRaise_alias h₁ h₂ ?_ (by simp [hp₁])
      rw [linkEnvRX_none hp₁]
      have hn₂ : n₂ ∈ P.names ++ env.names := by
        rcases List.mem_append.mp hm₂ with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (names_extern h)
      rw [hm] at hq₁ hq₂
      exact hS.alias n₁ ((hiff n₁).mp hm₁) n₂ hn₂ a hq₁ hq₂ hp₁ hp₂

section
variable {P : Program} {env : XEnv} {R : State → XOutcome} {E : XEnv}
  (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvRX P env R).extern n)
include hEb

/-- A raise of a base extern by a `call` is the same raise in the program without functions. -/
theorem callRaise_linkR {mem : Mem} {fr : Frame} {fn : FnRef} {args : List ValueId}
    {em : Exn × Mem} (h : callRaise env P mem fr fn args = some em) :
    callRaise E P.bare mem fr fn args = some em := by
  rw [callRaise_eq] at h ⊢
  cases hc : Opt.callArgs fr fn args with
  | ok q =>
    obtain ⟨ext, vals⟩ := q
    rw [hc] at h
    dsimp only at h ⊢
    unfold extRaise at h ⊢
    cases hp : P.func? ext.name with
    | some g => rw [hp] at h; cases h
    | none =>
      rw [hp] at h
      simp only [Program.bare_func?, hEb _ hp, linkEnvRX_none hp]
      exact h
  | trap c => rw [hc] at h; cases h
  | stuck m => rw [hc] at h; cases h

/-- A raise of a base extern by a `call_indirect` is the same raise in the program without
functions. -/
theorem callIndRaise_linkR {syms : String → Option Nat} (hS : IndScopeX P env syms)
    (hEn : E.names = (linkEnvRX P env R).names) (hEs : E.sigOf = (linkEnvRX P env R).sigOf)
    {mem : Mem} (hm : mem.symbols = syms) {fr : Frame} {sig : Nat} {callee : ValueId}
    {args : List ValueId} {em : Exn × Mem} (h : callIndRaise env P mem fr sig callee args = some em) :
    callIndRaise E P.bare mem fr sig callee args = some em := by
  unfold callIndRaise at h ⊢
  split at h
  · rename_i d a v hpre
    simp only [Program.bare_funcs, List.find?_nil]
    split at h
    · cases h
    · rename_i hnone
      rw [externAtRaise_congr (E₂ := linkEnvRX P env R) hEn
        (fun n hq => hEb n (func?_none_of_find hnone hq)) (fun n _ => by rw [hEs])]
      rcases externAtRaise_eq (R := R) (d := d) (vals := v) hS hm hnone with he | ⟨hn, -⟩
      · rw [he]; exact h
      · rw [hn] at h; cases h
  · cases h

/-- **A raise of a base extern is the same raise in the program without functions**, from a frame
of `f`. -/
theorem raiseAt_linkR {f : Function} {syms : String → Option Nat} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hf : f ∈ P.funcs) (hio : ¬ IndFree f → IndScopeX P env syms)
    (hEn : E.names = (linkEnvRX P env R).names) (hEs : E.sigOf = (linkEnvRX P env R).sigOf)
    {s : State} (hIf : LFrame (P.only f) s.frame) (hsy : ¬ IndFree f → s.mem.symbols = syms)
    {em : Exn × Mem} (h : raiseAt? env P s = some em) : raiseAt? E P.bare s = some em := by
  have hff : s.frame.func = f := by simpa [Program.only] using hIf.1
  have hI : LFrame P s.frame := ⟨by rw [hff]; exact hf, hIf.2⟩
  have hind : ∀ sig callee args, callIndRaise env P s.mem s.frame sig callee args = some em →
      (¬ IndFree f) → callIndRaise E P.bare s.mem s.frame sig callee args = some em :=
    fun _ _ _ h hnf => callIndRaise_linkR hEb (hio hnf) hEn hEs (hsy hnf) h
  revert h
  unfold raiseAt?
  cases hb : s.frame.body with
  | cons st rest =>
    dsimp only
    cases hi : st.inst with
    | call fn args => exact callRaise_linkR hEb
    | callIndirect sig callee args =>
      intro h
      refine hind sig callee args h fun hif => ?_
      obtain ⟨B, hB, hsuf, -⟩ | ⟨hnil, -⟩ := hI.2
      · rw [hff] at hB
        exact absurd hi ((hif B hB).1 st (hsuf.subset (by rw [hb]; simp)) sig callee args)
      · rw [hnil] at hb; cases hb
    | _ => dsimp only; intro h; cases h
  | nil =>
    dsimp only
    cases ht : s.frame.term with
    | returnCall fn args =>
      intro _
      obtain ⟨B, hB, -, hbt⟩ | ⟨-, bc, hbt⟩ := hI.2
      · exact absurd (hbt.symm.trans ht) (hP _ hI.1 B hB fn args)
      · rw [hbt] at ht; cases ht
    | tryCall fn args et =>
      dsimp only
      intro h
      rw [tryCallRaise_eq] at h ⊢
      cases hp : tryPre s.frame fn et with
      | ok q => rw [hp] at h; exact callRaise_linkR hEb h
      | trap c => rw [hp] at h; cases h
      | stuck m => rw [hp] at h; cases h
    | tryCallIndirect callee args et =>
      dsimp only
      intro h
      unfold tryCallIndRaise at h ⊢
      split at h
      · rename_i q hpre
        refine hind _ callee args h fun hif => ?_
        obtain ⟨B, hB, -, hbt⟩ | ⟨-, bc, hbt⟩ := hI.2
        · rw [hff] at hB
          exact absurd (hbt.symm.trans ht) ((hif B hB).2 callee args et)
        · rw [hbt] at ht; cases ht
      · cases h
    | _ => dsimp only; intro h; cases h

end

theorem callIndRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (sig : Nat)
    (callee : ValueId) (args : List ValueId) :
    callIndRaise env p mem fr sig callee args = match indPre fr sig callee args with
      | .ok (d, a, v) =>
        match p.funcs.find? fun g => (mem.symbols g.name) == some a with
        | some _ => none
        | none => externAtRaise env p mem d a v
      | _ => none := by
  unfold callIndRaise indPre
  rfl

theorem tryCallIndRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (callee : ValueId)
    (args : List ValueId) (et : ExnTable) :
    tryCallIndRaise env p mem fr callee args et = match tryIndPre fr et with
      | .ok _ => callIndRaise env p mem fr et.sig callee args
      | _ => none := by
  unfold tryCallIndRaise tryIndPre
  rfl

theorem indPre_tryState (s : State) (bc : BlockCall) (sig : Nat) (callee : ValueId)
    (args : List ValueId) :
    indPre (tryState s bc).frame sig callee args = indPre s.frame sig callee args := by
  simp only [indPre, tryState, Frame.getMany_with]
  rfl

/-! ## The linking theorem with callee runs `R` -/

/-- **Linking at the CLIF level with unwinding and callee runs `R`** (`runLoop_linkR` with
unwinding): a complete whole-program run with unwinding of at most `F + 1` steps from a state `xs`
reachable from `s0` (with `f`'s frames, `LInv (P.only f)`) that returns, traps or unwinds is a run
of the program without functions (`P.bare`) with the same outcome, whose calls of the program's
functions — `f` itself included — are atomic: `R` from the callee's entry (an `unwound` result
raised at the call), when `R` is the callee's whole-program run there for every callee entered
from a state reachable from `s0` whose run ends within `F` steps (`hR`). Indirect calls resolve
through the linked environment's names (`IndScopeX`); the environment `E` may omit what `f`
cannot call (as `runLoop_linkR`). -/
theorem runLoopX_linkR {P : Program} {env : XEnv} {f : Function} {syms : String → Option Nat}
    (R : State → XOutcome) (F : Nat) (s0 : XState) (hnd : (P.funcs.map (·.name)).Nodup)
    (hf : f ∈ P.funcs) (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hio : ¬ IndFree f → IndScopeX P env syms) {E : XEnv}
    (hEn : E.names = (linkEnvRX P env R).names) (hEs : E.sigOf = (linkEnvRX P env R).sigOf)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvRX P env R).extern n)
    (hEp : ∀ h ∈ P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvRX P env R).extern h.name)
    (hR : ∀ (t0 : State) (K : List (Frame × List ValueId)) (T : List (Option ExnTable)) (n : Nat),
      K ≠ [] → XInv P t0.toX → ReachesX env P s0 (t0.toX.below K T) → n ≤ F →
      (∀ msg, runLoopX env P n t0.toX ≠ .stuck msg) → runLoopX env P n t0.toX ≠ .outOfFuel →
      R t0 = runLoopX env P n t0.toX) :
    ∀ (N : Nat) (xs : XState), N ≤ F + 1 → ReachesX env P s0 xs → XInv P xs →
      LInv (P.only f) xs.s → (¬ IndFree f → xs.s.mem.symbols = syms) →
      (∀ msg, runLoopX env P N xs ≠ .stuck msg) → runLoopX env P N xs ≠ .outOfFuel →
      ∃ m, runLoopX E P.bare m xs = runLoopX env P N xs := by
  have hPf : ∀ g ∈ (P.only f).funcs, LinkFree g := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hP g hf
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro xs hNM hre hI hIf hsy hst hof
  cases N with
  | zero => exact absurd rfl hof
  | succ N =>
  have hff : xs.s.frame.func = f := by simpa [Program.only] using hIf.1.1
  -- a per-function step `r` after which the whole-program run continues with `n` steps
  have helper : ∀ (r : XStepResult) (n : Nat), n < N + 1 →
      stepX E P.bare xs = r → runLoopX env P (N + 1) xs = afterStepX env P n r →
      (∀ xs1, r = .next xs1 → ReachesX env P xs xs1) →
      ∃ m, runLoopX E P.bare m xs = runLoopX env P (N + 1) xs := by
    intro r n hn hr hrun hreach
    cases r with
    | next xs1 =>
      rw [hrun] at hst hof ⊢
      have h1 := hreach xs1 rfl
      have hIf1 : XInv (P.only f) xs1 :=
        stepX_next_xinv hPf ⟨hIf, hI.2⟩ hr (fun _ h => by simp at h)
      obtain ⟨m, hm⟩ := ih n hn xs1 (by omega) (hre.trans h1) (h1.xinv hP hI) hIf1.1
        (fun hnf => (h1.symbols hP (hio hnf).keep (hio hnf).keepU hI).trans (hsy hnf)) hst hof
      exact ⟨m + 1, by rw [runLoopX_succ', hr]; exact hm⟩
    | _ => exact ⟨0 + 1, by rw [runLoopX_succ', hr, hrun]; rfl⟩
  -- the steps that do not call a function of `P` are the same
  have same : stepX E P.bare xs = stepX env P xs →
      ∃ m, runLoopX E P.bare m xs = runLoopX env P (N + 1) xs := fun h =>
    helper _ N (by omega) h (runLoopX_succ' ..) fun xs1 hs1 => .next hs1 (.refl _)
  -- a raise of a base extern is the same raise
  cases hra : raiseAt? env P xs.s with
  | some em =>
    exact same (by simp only [stepX, raiseAt_linkR hEb hP hf hio hEn hEs hIf.1 hsy hra, hra])
  | none =>
  have ew : stepX env P xs = liftStep xs (step env.toEnv P xs.s) := by simp only [stepX, hra]
  -- an atomic call of `g` from `t` (whose frame is `xs`'s up to `body`/`term`)
  have atomic : ∀ (t : State) rest rs (g : Function) vals, g ∈ P.funcs →
      t.callers = xs.s.callers → t.frame.func = xs.s.frame.func →
      t.frame.regs = xs.s.frame.regs → t.frame.slots = xs.s.frame.slots →
      step env.toEnv P xs.s = StepResult.ofRes (enterFunc g vals t.mem) (fun (fr', mem') =>
        .next { frame := fr', callers := ({ t.frame with body := rest }, rs) :: t.callers,
                mem := mem' }) →
      (∀ fr' mem', enterFunc g vals t.mem = .ok (fr', mem') →
        (∀ rvals mem2, R ⟨fr', [], mem'⟩ = .returned rvals mem2 →
          rvals.map (·.ty) = AbiParam.tys g.sig.returns →
          stepX E P.bare xs = liftStep xs (continueWith t rest rs rvals mem2)) ∧
        (∀ c, R ⟨fr', [], mem'⟩ = .trapped c → stepX E P.bare xs = .trapped c) ∧
        (∀ e m, R ⟨fr', [], mem'⟩ = .unwound e m → stepX E P.bare xs = raiseIn xs e m)) →
      ∃ m, runLoopX E P.bare m xs = runLoopX env P (N + 1) xs := by
    intro t rest rs g vals hgP htc htf htr hts e1 e2
    cases he : enterFunc g vals t.mem with
    | trap c => exact absurd he (Opt.enterFunc_not_trap g vals t.mem c)
    | stuck m =>
      have hm : stepX env P xs = .stuck m := by rw [ew, e1, he]; rfl
      rw [runLoopX_succ', hm] at hst
      exact absurd rfl (hst m)
    | ok a =>
      obtain ⟨fr', mem'⟩ := a
      obtain ⟨e2r, e2t, e2u⟩ := e2 fr' mem' he
      let K : List (Frame × List ValueId) := ({ t.frame with body := rest }, rs) :: xs.s.callers
      let T : List (Option ExnTable) := pendingOf xs.s :: xs.tries
      let t0 : State := ⟨fr', [], mem'⟩
      have hw1 : stepX env P xs = .next (t0.toX.below K T) := by
        rw [ew, e1, he]
        simp only [StepResult.ofRes, liftStep, htc, List.length_cons]
        rfl
      have hwN : runLoopX env P (N + 1) xs = runLoopX env P N (t0.toX.below K T) := by
        rw [runLoopX_succ', hw1]; rfl
      rw [hwN] at hst hof
      have hsubI : XInv P t0.toX := ⟨⟨LFrame.enterFunc hgP he, fun _ h => by cases h⟩, rfl⟩
      have hfr' : fr'.func = g := by
        obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
        rw [hfr]
      have hreach0 : ReachesX env P xs (t0.toX.below K T) := .next hw1 (.refl _)
      have hRK := hR t0 K T N (List.cons_ne_nil _ _) hsubI (hre.trans hreach0) (by omega)
      cases hsub : runLoopX env P N t0.toX with
      | returned rvals mem2 =>
        obtain ⟨j, hj0, hjN, hj⟩ := runLoopX_below_returned hP env N t0.toX rvals mem2 hsubI hsub
        have hjj := hj K T (N - j)
        rw [show N - j + j = N by omega] at hjj
        rw [hjj] at hst
        have hlim : R t0 = .returned rvals mem2 := by
          rw [hRK (by rw [hsub]; exact fun _ h => by cases h)
            (by rw [hsub]; exact fun h => by cases h), hsub]
        have hty := runLoopX_returned_tys hP N t0.toX rvals mem2 hsubI hsub
        simp only [t0, State.toX, State.bottom, List.getLast?_nil, Option.map_none,
          Option.getD_none, hfr'] at hty
        have e2' := e2r rvals mem2 hlim hty
        cases hset : t.frame.regs.setMany rs rvals with
        | none =>
          simp only [resumeStepX, resumeStep, K, hset, afterStepX] at hst
          exact absurd rfl (hst _)
        | some regs =>
          have hres : resumeStepX K T rvals mem2 =
              .next ⟨⟨{ t.frame with regs, body := rest }, xs.s.callers, mem2⟩, xs.tries⟩ := by
            simp only [resumeStepX, resumeStep, K, T, hset, List.tail_cons]
          have hpstep : stepX E P.bare xs =
              .next ⟨⟨{ t.frame with regs, body := rest }, xs.s.callers, mem2⟩, xs.tries⟩ := by
            rw [e2']
            simp [continueWith, hset, liftStep, htc]
          obtain ⟨u, hu, hdone⟩ := runLoopX_returned_reaches env P N t0.toX rvals mem2 hsub
          refine helper _ (N - j) (by omega) hpstep (by rw [hwN, hjj, hres]) fun xs1 h1 => ?_
          cases h1
          exact (hreach0.trans (hu.under hP K T hsubI)).snoc
            (by rw [stepX_below hP (hu.xinv hP hsubI), hdone]; exact hres)
      | unwound e2 mem2 =>
        obtain ⟨j, hj0, hjN, hj⟩ := runLoopX_below_unwound hP env N t0.toX e2 mem2 hsubI hsub
        have hjj := hj K T (N - j)
        rw [show N - j + j = N by omega] at hjj
        have hlim : R t0 = .unwound e2 mem2 := by
          rw [hRK (by rw [hsub]; exact fun _ h => by cases h)
            (by rw [hsub]; exact fun h => by cases h), hsub]
        have hpstep : stepX E P.bare xs = resumeUnwind e2 K T mem2 := by
          rw [e2u e2 mem2 hlim]
          exact raiseIn_eq_resumeUnwind (xs := xs) (c := { t.frame with body := rest }) rs
            e2 mem2 htf htr hts
        obtain ⟨u, hu, hdone⟩ := runLoopX_unwound_reaches env P N t0.toX e2 mem2 hsub
        exact helper _ (N - j) (by omega) hpstep (by rw [hwN, hjj]) fun xs1 h1 =>
          (hreach0.trans (hu.under hP K T hsubI)).snoc
            (by rw [stepX_below hP (hu.xinv hP hsubI), hdone]; exact h1)
      | trapped c =>
        have hne1 : ∀ vals mem, runLoopX env P N t0.toX ≠ .returned vals mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        have hne2 : ∀ e mem, runLoopX env P N t0.toX ≠ .unwound e mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        have hlim : R t0 = .trapped c := by
          rw [hRK (by rw [hsub]; exact fun _ h => by cases h)
            (by rw [hsub]; exact fun h => by cases h), hsub]
        refine ⟨1, ?_⟩
        rw [hwN, runLoopX_below_of_not_ended hP env K T N t0.toX hsubI hne1 hne2, hsub,
          runLoopX_succ', e2t c hlim]
        rfl
      | stuck msg =>
        have hne1 : ∀ vals mem, runLoopX env P N t0.toX ≠ .returned vals mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        have hne2 : ∀ e mem, runLoopX env P N t0.toX ≠ .unwound e mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        rw [runLoopX_below_of_not_ended hP env K T N t0.toX hsubI hne1 hne2, hsub] at hst
        exact absurd rfl (hst msg)
      | outOfFuel =>
        have hne1 : ∀ vals mem, runLoopX env P N t0.toX ≠ .returned vals mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        have hne2 : ∀ e mem, runLoopX env P N t0.toX ≠ .unwound e mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        rw [runLoopX_below_of_not_ended hP env K T N t0.toX hsubI hne1 hne2, hsub] at hof
        exact absurd rfl hof
  -- a call (`callCont`) from `t`, including a direct self call
  have call : ∀ (t : State) rest rs ext vals, t.callers = xs.s.callers → t.mem = xs.s.mem →
      t.frame.func = xs.s.frame.func → t.frame.regs = xs.s.frame.regs →
      t.frame.slots = xs.s.frame.slots → ext.name ∈ f.externs.map (·.2.name) →
      step env.toEnv P xs.s = Opt.callCont env.toEnv P t rest rs ext vals →
      step E.toEnv P.bare xs.s = Opt.callCont E.toEnv P.bare t rest rs ext vals →
      raiseAt? E P.bare xs.s = extRaise E P.bare xs.s.mem ext vals →
      extRaise env P xs.s.mem ext vals = none →
      ∃ m, runLoopX E P.bare m xs = runLoopX env P (N + 1) xs := by
    intro t rest rs ext vals htc htm htf htr hts hext e1 e2 e3 hw
    cases hpf : P.func? ext.name with
    | none =>
      have hx : extRaise E P.bare xs.s.mem ext vals = none := by
        rw [← hw]
        unfold extRaise
        simp only [Program.bare_func?, hEb _ hpf, linkEnvRX_none hpf, hpf]
      have hEt : E.toEnv.extern ext.name = env.toEnv.extern ext.name := by
        simp only [XEnv.toEnv, hEb _ hpf, linkEnvRX_none hpf]
      apply same
      simp only [stepX, e3, hx, hra, e1, e2]
      simp only [Opt.callCont, hpf, Program.bare_func?, hEt]
    | some g =>
      obtain ⟨hgP, hgn⟩ := Program.func?_some hpf
      have hEg : E.extern ext.name = (linkEnvRX P env R).extern ext.name := by
        rw [← hgn]
        exact hEp g hgP (.inl (by rw [hgn]; exact hext))
      cases hsig : (AbiParam.tys g.sig.params == AbiParam.tys ext.sig.params &&
          AbiParam.tys g.sig.returns == AbiParam.tys ext.sig.returns) with
      | false =>
        obtain ⟨msg, hm⟩ : ∃ msg, stepX env P xs = .stuck msg := by
          rw [ew, e1]
          simp only [Opt.callCont, hpf, hsig, Bool.false_eq_true, ↓reduceIte, liftStep]
          exact ⟨_, rfl⟩
        rw [runLoopX_succ', hm] at hst
        exact absurd rfl (hst msg)
      | true =>
        have hsig2 := hsig
        simp only [Bool.and_eq_true, beq_iff_eq] at hsig2
        refine atomic t rest rs g vals hgP htc htf htr hts
          (by rw [e1]; simp only [Opt.callCont, hpf, hsig, ↓reduceIte])
          fun fr' mem' he => ?_
        have hinit : initState P ext.name vals t.mem = .ok ⟨fr', [], mem'⟩ := by
          simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
        have hx : ∀ o, R ⟨fr', [], mem'⟩ = o → extRaise E P.bare xs.s.mem ext vals =
            match o with
            | .unwound e m => some (e, m)
            | _ => none := by
          intro o ho
          rw [← htm]
          unfold extRaise
          simp only [Program.bare_func?, hEg, linkEnvRX_some hpf, hinit, ho]
          cases o <;> rfl
        refine ⟨fun rvals mem2 hlim hty => ?_, fun c hlim => ?_, fun e m hlim => ?_⟩
        · simp only [stepX, e3, hx _ hlim, e2]
          simp only [Opt.callCont, Program.bare_func?, XEnv.toEnv, hEg, linkEnvRX_some hpf,
            Option.map_some, hinit, hlim, XOutcome.toOutcome, hty, hsig2.2, beq_self_eq_true,
            ↓reduceIte]
        · simp only [stepX, e3, hx _ hlim, e2]
          simp only [Opt.callCont, Program.bare_func?, XEnv.toEnv, hEg, linkEnvRX_some hpf,
            Option.map_some, hinit, hlim, XOutcome.toOutcome, liftStep]
        · simp only [stepX, e3, hx _ hlim]
  -- an indirect call (`indCont`) from `t`, a frame of `f`
  have ind : ∀ (t : State) rest rs sig d a v, t.callers = xs.s.callers → t.mem = xs.s.mem →
      t.frame.func = xs.s.frame.func → t.frame.regs = xs.s.frame.regs →
      t.frame.slots = xs.s.frame.slots → IndSig f d →
      step env.toEnv P xs.s = indCont env.toEnv P t rest rs sig d a v →
      step E.toEnv P.bare xs.s = indCont E.toEnv P.bare t rest rs sig d a v →
      raiseAt? E P.bare xs.s = externAtRaise E P.bare t.mem d a v →
      (match P.funcs.find? fun g => (t.mem.symbols g.name) == some a with
        | some _ => none
        | none => externAtRaise env P t.mem d a v) = none →
      ∃ m, runLoopX E P.bare m xs = runLoopX env P (N + 1) xs := by
    intro t rest rs sig d a v htc htm htf htr hts hdS e1 e2 e3 hw
    have hnf : ¬ IndFree f := hdS.not_indFree
    have hS := hio hnf
    have hm : t.mem.symbols = syms := htm ▸ hsy hnf
    cases hfind : P.funcs.find? (fun g => t.mem.symbols g.name == some a) with
    | none =>
      rw [hfind] at hw
      dsimp only at hw
      have hcg : callExternAt E.toEnv P.bare t.mem d a v =
          callExternAt (linkEnvRX P env R).toEnv P.bare t.mem d a v :=
        callExternAt_congr hEn
          (fun n hq => by simp only [XEnv.toEnv, hEb n (func?_none_of_find hfind hq)])
          (fun n _ => by simp only [XEnv.toEnv, hEs])
      have hrg : externAtRaise E P.bare t.mem d a v =
          externAtRaise (linkEnvRX P env R) P.bare t.mem d a v :=
        externAtRaise_congr hEn (fun n hq => hEb n (func?_none_of_find hfind hq))
          (fun n _ => by rw [hEs])
      rw [linkEnvRX_toEnv] at hcg
      have hstuck : ∀ m₂, callExternAt env.toEnv P t.mem d a v = .stuck m₂ → False := by
        intro m₂ h₂
        have : stepX env P xs = .stuck m₂ := by
          rw [ew, e1]
          simp only [indCont, hfind, h₂, StepResult.ofRes_stuck, liftStep]
        rw [runLoopX_succ', this] at hst
        exact hst _ rfl
      rcases callExternAt_eq (R := fun s => (R s).toOutcome) (d := d) (vals := v) hS.toScope hm
        hfind with he | ⟨m₂, h₂⟩
      · rcases externAtRaise_eq (R := R) (d := d) (vals := v) hS hm hfind with hr | ⟨-, m₃, h₃⟩
        · apply same
          rw [ew, e1]
          simp only [stepX, e3, hrg, hr, hw, e2, indCont, hfind, Program.bare_funcs,
            List.find?_nil, hcg, he]
        · exact (hstuck m₃ h₃).elim
      · exact (hstuck m₂ h₂).elim
    | some h =>
      have hhP := List.mem_of_find?_eq_some hfind
      have hha : t.mem.symbols h.name = some a := by simpa using List.find?_some hfind
      have hname : (E.names ++ P.bare.externNames).find?
          (fun n => t.mem.symbols n == some a) = some h.name := by
        simp only [hEn, linkEnvRX_names, Program.bare_externNames, List.append_nil, Program.names,
          List.append_assoc, List.find?_append, List.find?_map, Function.comp_def, hfind,
          Option.map_some, Option.some_or]
      have hpf : P.func? h.name = some h := by
        cases e : P.func? h.name with
        | none => exact absurd rfl (Program.func?_none e h hhP)
        | some g =>
          obtain ⟨hg, hgn⟩ := Program.func?_some e
          rw [name_inj hnd hg hhP hgn]
      cases hsig : d.abiMatch h.sig with
      | false =>
        have : stepX env P xs = .stuck s!"call_indirect sig{sig}: signature does not match %{h.name}" := by
          rw [ew, e1]
          simp only [indCont, hfind, hsig, Bool.false_eq_true, ↓reduceIte, liftStep]
        rw [runLoopX_succ', this] at hst
        exact absurd rfl (hst _)
      | true =>
        have hsig' := Signature.abiMatch_eq_true.mp hsig
        have hEh : E.extern h.name = (linkEnvRX P env R).extern h.name :=
          hEp h hhP (.inr ⟨by rw [← hm, hha]; exact Option.some_ne_none a, d, hdS, hsig⟩)
        refine atomic t rest rs h v hhP htc htf htr hts
          (by rw [e1]; simp only [indCont, hfind, hsig, ↓reduceIte]) fun fr' mem' he => ?_
        have hinit : initState P h.name v t.mem = .ok ⟨fr', [], mem'⟩ := by
          simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
        have hvt : v.map (·.ty) = AbiParam.tys d.params := by
          obtain ⟨_, _, _, h1, -⟩ := Opt.enterFunc_ok he
          rw [h1, hsig'.1]
        have hx : ∀ o, R ⟨fr', [], mem'⟩ = o → externAtRaise E P.bare t.mem d a v =
            match o with
            | .unwound e m => some (e, m)
            | _ => none := by
          intro o ho
          simp only [externAtRaise, hname, hEh, linkEnvRX_some hpf, hEs, linkEnvRX_sigOf, hpf,
            Option.map_some, Option.all_some, hsig, hvt, beq_self_eq_true, Bool.and_self,
            ↓reduceIte, hinit, ho]
          cases o <;> rfl
        refine ⟨fun rvals mem2 hlim hty => ?_, fun c hlim => ?_, fun e m hlim => ?_⟩
        · simp only [stepX, e3, hx _ hlim, e2]
          simp only [indCont, Program.bare_funcs, List.find?_nil, callExternAt, hname,
            Res.ofOption_some, Res.ok_bind, XEnv.toEnv, hEh, linkEnvRX_some hpf, hEs,
            linkEnvRX_sigOf, hpf, Option.map_some, Option.all_some, hsig, checkTys, hvt,
            beq_self_eq_true, Res.check_true, hinit, hlim, XOutcome.toOutcome, hty, hsig'.2.2,
            ↓reduceIte, Res.pure_eq, StepResult.ofRes_ok]
        · simp only [stepX, e3, hx _ hlim, e2]
          simp only [indCont, Program.bare_funcs, List.find?_nil, callExternAt, hname,
            Res.ofOption_some, Res.ok_bind, XEnv.toEnv, hEh, linkEnvRX_some hpf, hEs,
            linkEnvRX_sigOf, hpf, Option.map_some, Option.all_some, hsig, checkTys, hvt,
            beq_self_eq_true, Res.check_true, hinit, hlim, XOutcome.toOutcome,
            StepResult.ofRes_trap, liftStep]
        · simp only [stepX, e3, hx _ hlim]
  -- the shapes of the step
  rcases step_shape xs.s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · -- a `try_call`: its preludes are the same, then the call from the waiting frame
    have e1 := step_try env.toEnv P xs.s hb ht
    have e2 := step_try E.toEnv P.bare xs.s hb ht
    have r1 : raiseAt? env P xs.s = tryCallRaise env P xs.s.mem xs.s.frame fn args et := by
      simp only [raiseAt?, hb, ht]
    have r2 : raiseAt? E P.bare xs.s = tryCallRaise E P.bare xs.s.mem xs.s.frame fn args et := by
      simp only [raiseAt?, hb, ht]
    rw [tryCallRaise_eq] at r1 r2
    cases hpre : tryPre xs.s.frame fn et with
    | trap c =>
      apply same
      simp only [stepX, r2, hpre, hra, e1, e2, StepResult.ofRes]
    | stuck m =>
      apply same
      simp only [stepX, r2, hpre, hra, e1, e2, StepResult.ofRes]
    | ok q =>
      obtain ⟨n, b, bc⟩ := q
      rw [hpre] at r1 r2 e1 e2
      simp only [StepResult.ofRes] at e1 e2
      rw [callRaise_eq] at r1 r2
      have hca := callArgs_tryState xs.s bc fn args
      cases hc : Opt.callArgs xs.s.frame fn args with
      | trap c =>
        apply same
        simp only [stepX, r2, hc, hra, e1, e2, hca]
      | stuck m =>
        apply same
        simp only [stepX, r2, hc, hra, e1, e2, hca]
      | ok q =>
        obtain ⟨ext, vals⟩ := q
        rw [hc] at r1 r2
        dsimp only at r1 r2
        rw [hca, hc] at e1 e2
        simp only at e1 e2
        have hext : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hc
        exact call (tryState xs.s bc) [] _ ext vals rfl rfl rfl rfl rfl (lookup_name_mem hext)
          e1 e2 r2 (by rw [← r1]; exact hra)
  · -- a `try_call_indirect`
    have e1 := step_tryInd env.toEnv P xs.s hb ht
    have e2 := step_tryInd E.toEnv P.bare xs.s hb ht
    have r1 : raiseAt? env P xs.s = tryCallIndRaise env P xs.s.mem xs.s.frame callee args et := by
      simp only [raiseAt?, hb, ht]
    have r2 : raiseAt? E P.bare xs.s = tryCallIndRaise E P.bare xs.s.mem xs.s.frame callee args et := by
      simp only [raiseAt?, hb, ht]
    rw [tryCallIndRaise_eq] at r1 r2
    cases hpre : tryIndPre xs.s.frame et with
    | trap c =>
      apply same
      simp only [stepX, r2, hpre, hra, e1, e2, StepResult.ofRes]
    | stuck m =>
      apply same
      simp only [stepX, r2, hpre, hra, e1, e2, StepResult.ofRes]
    | ok q =>
      obtain ⟨n, b, bc⟩ := q
      rw [hpre] at r1 r2 e1 e2
      simp only [StepResult.ofRes] at e1 e2
      rw [callIndRaise_eq] at r1 r2
      have hpi := indPre_tryState xs.s bc et.sig callee args
      cases hc : indPre xs.s.frame et.sig callee args with
      | trap c =>
        apply same
        simp only [stepX, r2, hc, hra, e1, e2, hpi]
      | stuck m =>
        apply same
        simp only [stepX, r2, hc, hra, e1, e2, hpi]
      | ok q =>
        obtain ⟨d, a, v⟩ := q
        rw [hc] at r1 r2
        dsimp only at r1 r2
        rw [hpi, hc] at e1 e2
        simp only at e1 e2
        simp only [Program.bare_funcs, List.find?_nil] at r2
        have hdS : IndSig f d := by
          have hl := indPre_lookup hc
          rcases hIf.1 with ⟨-, ⟨b0, hb0, -, ht0⟩ | ⟨-, bc0, ht0⟩⟩
          · rw [hff] at hb0
            refine ⟨b0, hb0, .inr ⟨callee, args, et, ht0.symm.trans ht, ?_⟩⟩
            rw [← hff]; exact hl
          · rw [ht] at ht0; cases ht0
        exact ind (tryState xs.s bc) [] _ et.sig d a v rfl rfl rfl rfl rfl hdS e1 e2 r2
          (by have := hra; rw [r1] at this; exact this)
  · -- a `call_indirect` statement
    have e1 := step_ind env.toEnv P xs.s hb hi
    have e2 := step_ind E.toEnv P.bare xs.s hb hi
    have r1 : raiseAt? env P xs.s = callIndRaise env P xs.s.mem xs.s.frame sig callee args := by
      simp only [raiseAt?, hb, hi]
    have r2 : raiseAt? E P.bare xs.s = callIndRaise E P.bare xs.s.mem xs.s.frame sig callee args := by
      simp only [raiseAt?, hb, hi]
    rw [callIndRaise_eq] at r1 r2
    cases hc : indPre xs.s.frame sig callee args with
    | trap c =>
      apply same
      simp only [stepX, r2, hc, hra, e1, e2, StepResult.ofRes]
    | stuck m =>
      apply same
      simp only [stepX, r2, hc, hra, e1, e2, StepResult.ofRes]
    | ok q =>
      obtain ⟨d, a, v⟩ := q
      rw [hc] at r1 r2 e1 e2
      dsimp only at r1 r2
      simp only [StepResult.ofRes] at e1 e2
      simp only [Program.bare_funcs, List.find?_nil] at r2
      have hdS : IndSig f d := by
        have hl := indPre_lookup hc
        rcases hIf.1 with ⟨-, ⟨b0, hb0, hsuf, -⟩ | ⟨hnil, -⟩⟩
        · rw [hff] at hb0
          refine ⟨b0, hb0, .inl ⟨st, hsuf.subset (by rw [hb]; simp), sig, callee, args, hi, ?_⟩⟩
          rw [← hff]; exact hl
        · rw [hnil] at hb; cases hb
      exact ind xs.s rest st.results sig d a v rfl rfl rfl rfl rfl hdS e1 e2 r2
        (by rw [← r1]; exact hra)
  · have e1 := Opt.step_eq_lift env.toEnv P xs.s hci
    have e2 := Opt.step_eq_lift E.toEnv P.bare xs.s hci
    have hlocal : (∀ ext vals rs rest, Opt.lstep xs.s.frame xs.s.mem ≠ .call ext vals rs rest) →
        ∃ m, runLoopX E P.bare m xs = runLoopX env P (N + 1) xs := by
      intro hnc
      have r2 : raiseAt? E P.bare xs.s = none := raiseAt_none_of_lstep hP hI.1.1 hci hnc
      apply same
      simp only [stepX, r2, hra, e1, e2]
      cases hl' : Opt.lstep xs.s.frame xs.s.mem with
      | call ext vals rs rest => exact absurd hl' (hnc ext vals rs rest)
      | tail ext vals => exact absurd hl' (lstep_ne_tail hP hI.1.1)
      | _ => rfl
    cases hl : Opt.lstep xs.s.frame xs.s.mem with
    | call ext vals rs rest =>
      obtain ⟨st, fn, args, hb, hi, -, hca⟩ := Opt.lstep_call_inv hl
      rw [hl] at e1 e2
      have r1 : raiseAt? env P xs.s = extRaise env P xs.s.mem ext vals := by
        simp only [raiseAt?, hb, hi, callRaise_eq, hca]
      have r2 : raiseAt? E P.bare xs.s = extRaise E P.bare xs.s.mem ext vals := by
        simp only [raiseAt?, hb, hi, callRaise_eq, hca]
      have hext : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hca
      exact call xs.s rest rs ext vals rfl rfl rfl rfl rfl (lookup_name_mem hext) e1 e2 r2
        (by rw [← r1]; exact hra)
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1.1)
    | _ => exact hlocal (fun _ _ _ _ h => by rw [hl] at h; cases h)

/-! ## Instances: bounded fuel, bounded depth -/

/-- **The environment of the per-function programs of `P` with unwinding and callee runs of at
most `M` steps** (`linkEnvN`'s counterpart). -/
def linkEnvNX (P : Program) (env : XEnv) (M : Nat) : XEnv :=
  linkEnvRX P env fun s => runLoopX env P M s.toX

/-- **Linking at the CLIF level with unwinding and bounded callee runs** (`runLoopX_linkR` with
`linkEnvNX P env M`): a complete whole-program run with unwinding of at most `M + 1` steps (from
a state of `f`'s frames) is a run of `P.bare` with the same outcome whose program calls are
atomic: the callee's whole-program run with unwinding of at most `M` steps. -/
theorem runLoopX_linkN {P : Program} {env : XEnv} {f : Function} {syms : String → Option Nat}
    (M : Nat) (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hio : ¬ IndFree f → IndScopeX P env syms) {E : XEnv}
    (hEn : E.names = (linkEnvNX P env M).names) (hEs : E.sigOf = (linkEnvNX P env M).sigOf)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvNX P env M).extern n)
    (hEp : ∀ h ∈ P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvNX P env M).extern h.name)
    (N : Nat) (xs : XState) (hN : N ≤ M + 1) (hI : XInv P xs) (hIf : LInv (P.only f) xs.s)
    (hsy : ¬ IndFree f → xs.s.mem.symbols = syms)
    (hst : ∀ msg, runLoopX env P N xs ≠ .stuck msg) (hof : runLoopX env P N xs ≠ .outOfFuel) :
    ∃ m, runLoopX E P.bare m xs = runLoopX env P N xs :=
  runLoopX_linkR _ M xs hnd hf hP hio hEn hEs hEb hEp
    (fun t0 _ _ n _ _ _ hn _ hof' => by
      have := runLoopX_add env P n t0.toX hof' (M - n)
      rwa [Nat.add_sub_cancel' hn] at this)
    N xs hN (.refl xs) hI hIf hsy hst hof

/-- **The call depth along a run with unwinding, decided**: the run from `xs` ends within `N`
steps and every state of it has at most `d` callers. -/
def depthBX (env : XEnv) (p : Program) (d : Nat) : Nat → XState → Bool
  | 0, _ => false
  | N + 1, xs => decide (xs.s.callers.length ≤ d) &&
      match stepX env p xs with
      | .next xs' => depthBX env p d N xs'
      | _ => true

theorem depthLeX_of_depthBX {env : XEnv} {p : Program} {d : Nat} :
    ∀ (N : Nat) (xs : XState), depthBX env p d N xs = true → DepthLeX env p d xs
  | 0, _, h => by simp [depthBX] at h
  | N + 1, xs, h => by
    simp only [depthBX, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    intro u hu
    cases hu with
    | refl => exact h1
    | next hs hu' =>
      rw [hs] at h2
      exact depthLeX_of_depthBX N _ h2 u hu'

open Classical in
/-- **The whole-program run with unwinding of fuel `F` with at most `d` nested calls**: the run
of `F` steps if every state the run reaches has at most `d - 1` callers, else `outOfFuel`. -/
noncomputable def runDX (env : XEnv) (P : Program) (F d : Nat) (s : State) : XOutcome :=
  if 0 < d ∧ DepthLeX env P (d - 1) s.toX then runLoopX env P F s.toX else .outOfFuel

/-- **The environment of the per-function programs of `P` with unwinding, callee runs of fuel
`F` and at most `d` nested levels** (`linkEnvRX` with `runDX`). -/
noncomputable def linkEnvDX (P : Program) (env : XEnv) (F d : Nat) : XEnv :=
  linkEnvRX P env (runDX env P F d)

/-- **Linking at the CLIF level with unwinding and callee runs of bounded depth**
(`runLoopX_linkR` with `linkEnvDX P env F d`): a complete whole-program run with unwinding of at
most `F + 1` steps from `xs` (of `f`'s frames) whose call depth is at most `d` (`DepthLeX`) is a
run of `P.bare` with the same outcome whose program calls are atomic: the callee's
whole-program run of fuel `F` with at most `d - 1` callers of its own (`runDX`). -/
theorem runLoopX_linkD {P : Program} {env : XEnv} {f : Function} {syms : String → Option Nat}
    (F d : Nat) (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hio : ¬ IndFree f → IndScopeX P env syms) {E : XEnv}
    (hEn : E.names = (linkEnvDX P env F d).names) (hEs : E.sigOf = (linkEnvDX P env F d).sigOf)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvDX P env F d).extern n)
    (hEp : ∀ h ∈ P.funcs, (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvDX P env F d).extern h.name)
    (N : Nat) (xs : XState) (hN : N ≤ F + 1) (hd : DepthLeX env P d xs) (hI : XInv P xs)
    (hIf : LInv (P.only f) xs.s) (hsy : ¬ IndFree f → xs.s.mem.symbols = syms)
    (hst : ∀ msg, runLoopX env P N xs ≠ .stuck msg) (hof : runLoopX env P N xs ≠ .outOfFuel) :
    ∃ m, runLoopX E P.bare m xs = runLoopX env P N xs :=
  runLoopX_linkR _ F xs hnd hf hP hio hEn hEs hEb hEp
    (fun t0 _ _ n hK hI0 hr hn _ hof' => by
      simp only [runDX, hd.callee hP hK hI0 hr, and_self, ↓reduceIte]
      have := runLoopX_add env P n t0.toX hof' (F - n)
      rwa [Nat.add_sub_cancel' hn] at this)
    N xs hN (.refl xs) hI hIf hsy hst hof

/-- The entry state of a whole-program run of `f` has only `f`'s frame. -/
theorem initState_linv_only {P : Program} {n : String} {vals : List Val} {mem : Mem} {s : State}
    {f : Function} (h : initState P n vals mem = .ok s) (hn : P.func? n = some f) :
    LInv (P.only f) s := by
  obtain ⟨-, hc, g, hg, mem', he, -⟩ := initState_symbols h
  rw [hn] at hg
  cases hg
  exact ⟨LFrame.enterFunc (by simp [Program.only]) he, by rw [hc]; simp⟩

/-! ## Non-vacuity

On `Clif.UnwindWitness` (`%main` `try_call`s `%mid`, which calls the unwinding extern `%throw`;
`%main`'s handler catches the exception, 105): the run of `%main` in the program without functions
(both `%mid` and `%main` itself atomic; `%mid`'s bounded whole-program run ends `unwound`, raised
at `%main`'s `try_call`) returns 105, as the whole-program run; `runLoopX_linkN` and
`runLoopX_linkD` apply to it (the depth: `depthBX`). -/

namespace UnwindLinkNWitness

open UnwindWitness UnwindLinkWitness

/-- The entry state of `%main` on 5. -/
def mainEntry? : Option State :=
  match prog.initMem with
  | .ok mem =>
    match initState prog "main" [⟨.i64, 5⟩] mem with
    | .ok s => some s
    | _ => none
  | _ => none

theorem main_entry_facts : mainEntry?.map (fun s =>
    ((runLoopX (env 7) prog 20 s.toX).returnedVals?,
      (runLoopX (linkEnvNX prog (env 7) 20) prog.bare 20 s.toX).returnedVals?,
      depthBX (env 7) prog 1 20 s.toX)) =
    some (some [⟨.i64, 105⟩], some [⟨.i64, 105⟩], true) := by
  decide +kernel

theorem main_entry : ∃ s mem, prog.initMem = .ok mem ∧
    initState prog "main" [⟨.i64, 5⟩] mem = .ok s ∧
    (runLoopX (env 7) prog 20 s.toX).returnedVals? = some [⟨.i64, 105⟩] ∧
    (runLoopX (linkEnvNX prog (env 7) 20) prog.bare 20 s.toX).returnedVals? =
      some [⟨.i64, 105⟩] ∧ depthBX (env 7) prog 1 20 s.toX = true := by
  have h := main_entry_facts
  unfold mainEntry? at h
  cases hm : prog.initMem with
  | ok mem =>
    rw [hm] at h
    dsimp only at h
    cases hi : initState prog "main" [⟨.i64, 5⟩] mem with
    | ok s =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨s, mem, rfl, hi, h⟩
    | trap c => rw [hi] at h; simp at h
    | stuck msg => rw [hi] at h; simp at h
  | trap c => rw [hm] at h; simp at h
  | stuck msg => rw [hm] at h; simp at h

/-- **`runLoopX_linkN` on the witness**: the run of `%main` in the program without functions,
every program call atomic (callee runs of at most 20 steps), returns 105 as the whole-program
run. -/
theorem linkN_caught : ∃ (xs : XState) (m : Nat),
    (runLoopX (linkEnvNX prog (env 7) 20) prog.bare m xs).returnedVals? = some [⟨.i64, 105⟩] ∧
    (runLoopX (env 7) prog 20 xs).returnedVals? = some [⟨.i64, 105⟩] := by
  obtain ⟨s, _, _, hi, h, -, -⟩ := main_entry
  have hr : runLoopX (env 7) prog 20 s.toX ≠ .outOfFuel := by
    intro e; rw [e] at h; cases h
  have hs : ∀ msg, runLoopX (env 7) prog 20 s.toX ≠ .stuck msg := by
    intro msg e; rw [e] at h; cases h
  obtain ⟨m, hm'⟩ := runLoopX_linkN (f := mainFn) (syms := fun _ => none) 20 prog_nodup
    (by simp [prog]) prog_linkFree (fun h => absurd (prog_indFree _ (by simp [prog])) h)
    rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl) 20 s.toX (by omega) (initState_xinv hi)
    (initState_linv_only hi (by decide)) (fun h => absurd (prog_indFree _ (by simp [prog])) h)
    hs hr
  exact ⟨s.toX, m, by rw [hm']; exact h, h⟩

/-- **`runLoopX_linkD` on the witness**: with call depth at most 1 (`%main` and `%mid`), the run
of `%main` in the program without functions under `linkEnvDX` returns 105 as the whole-program
run. -/
theorem linkD_caught : ∃ (xs : XState) (m : Nat),
    (runLoopX (linkEnvDX prog (env 7) 20 1) prog.bare m xs).returnedVals? = some [⟨.i64, 105⟩] ∧
    (runLoopX (env 7) prog 20 xs).returnedVals? = some [⟨.i64, 105⟩] := by
  obtain ⟨s, _, _, hi, h, -, hd⟩ := main_entry
  have hr : runLoopX (env 7) prog 20 s.toX ≠ .outOfFuel := by
    intro e; rw [e] at h; cases h
  have hs : ∀ msg, runLoopX (env 7) prog 20 s.toX ≠ .stuck msg := by
    intro msg e; rw [e] at h; cases h
  obtain ⟨m, hm'⟩ := runLoopX_linkD (f := mainFn) (syms := fun _ => none) 20 1 prog_nodup
    (by simp [prog]) prog_linkFree (fun h => absurd (prog_indFree _ (by simp [prog])) h)
    rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl) 20 s.toX (by omega)
    (depthLeX_of_depthBX 20 _ hd) (initState_xinv hi)
    (initState_linv_only hi (by decide)) (fun h => absurd (prog_indFree _ (by simp [prog])) h)
    hs hr
  exact ⟨s.toX, m, by rw [hm']; exact h, h⟩

end UnwindLinkNWitness

end Clif
