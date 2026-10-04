import FV.E2E.LinkClif

/-!
# Linking at the CLIF level with bounded callee runs

`linkEnv P base` runs a called function `g` of `P` with unbounded fuel (`runLim`). The Arm-level
linking (`FV/E2E/LinkArm.lean`) is an induction on the whole-program fuel, so it needs the
environment whose program callees run at most `M` steps (`linkEnvN P base M`; a callee that does
not finish within `M` steps is `outOfFuel`, which the caller treats as `stuck`).
`runLoop_linkN`: a complete whole-program run of at most `M + 1` steps is a complete
per-function run under `linkEnvN P base M` (`runLoop_link` with bounded callee runs: every
callee's sub-run is shorter than the whole run), also with `call_indirect`/`try_call_indirect`
(between functions of `P` too: the per-function program resolves a callee address through the
linked environment's names — every name of `P` and of the base environment — whatever `f`
declares, `IndScope`), and under any restriction of `linkEnvN` keeping the functions of `P`
the whole-program run of `f` can call (declared, or entered by an indirect call whose call-site
signature matches theirs, `Signature.abiMatch`).
-/

namespace Clif

/-- The names an indirect call of a function of `P` can resolve: the functions of `P` and the
externs they declare. -/
def Program.names (P : Program) : List String := P.funcs.map (·.name) ++ P.externNames

/-- **The environment of the per-function programs of `P` with callee runs of at most `M` steps**:
a call of a function `g` of `P` runs `g`'s whole-program run for at most `M` steps; every other
extern is `base`'s. An indirect call resolves its address among every name of `P` and of `base`
(`names`): a function of `P` is reached through a pointer whether or not the caller declares
it. -/
def linkEnvN (P : Program) (base : Env) (M : Nat) : Env where
  extern n := match P.func? n with
    | some _ => some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLoop base P M s
      | .trap c => .trapped c
      | .stuck m => .stuck m
    | none => base.extern n
  names := P.names ++ base.names

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

@[simp] theorem linkEnvN_names {P : Program} {base : Env} {M : Nat} :
    (linkEnvN P base M).names = P.names ++ base.names := rfl

/-! ## The link-time symbols -/

/-- Distinct names of `ns` have distinct link-time addresses. -/
def SymInj (ns : List String) (syms : String → Option Nat) : Prop :=
  ∀ a ∈ ns, ∀ b ∈ ns, ∀ x, syms a = some x → syms b = some x → a = b

/-- **The scope of indirect calls in the linked program**: the base externs keep the symbols,
the functions of `P` have distinct addresses, and names of `P` and of the base environment that
share an address of no function of `P` (aliases: one copy of code under several symbols, e.g.
folded by the linker) are the same extern of the base environment. -/
structure IndScope (P : Program) (base : Env) (syms : String → Option Nat) : Prop where
  keep : Opt.EnvKeepsSymbols base
  inj : SymInj (P.funcs.map (·.name)) syms
  alias : ∀ a ∈ P.names ++ base.names, ∀ b ∈ P.names ++ base.names, ∀ x, syms a = some x →
    syms b = some x → P.func? a = none → P.func? b = none → base.extern a = base.extern b

theorem enterFunc_symbols {g : Function} {vals : List Val} {mem mem' : Mem} {fr : Frame}
    (h : enterFunc g vals mem = .ok (fr, mem')) : mem'.symbols = mem.symbols := by
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok h
  have := (Opt.enterSlots_ids g mem).2
  rw [hal] at this
  exact this

theorem callCont_symbols {env : Env} {p : Program} {t : State} {rest : List Stmt}
    {rs : List ValueId} {ext : ExtFunc} {vals : List Val} {s1 : State}
    (hk : Opt.EnvKeepsSymbols env) (h : Opt.callCont env p t rest rs ext vals = .next s1) :
    s1.mem.symbols = t.mem.symbols := by
  unfold Opt.callCont at h
  split at h
  · split at h
    · obtain ⟨⟨fr', mem'⟩, he, h⟩ := Opt.StepResult.ofRes_eq_next h
      cases h
      exact enterFunc_symbols he
    · cases h
  · split at h
    · rename_i gsem hgs
      split at h
      · rename_i rvals mem' hr
        split at h
        · unfold continueWith at h
          split at h
          · cases h
            exact hk _ _ hgs _ _ _ _ hr
          · cases h
        · cases h
      all_goals cases h
    · cases h

theorem indCont_symbols {env : Env} {p : Program} {t : State} {rest : List Stmt}
    {rs : List ValueId} {sig : Nat} {d : Signature} {a : Nat} {v : List Val} {s1 : State}
    (hk : Opt.EnvKeepsSymbols env) (h : indCont env p t rest rs sig d a v = .next s1) :
    s1.mem.symbols = t.mem.symbols := by
  rcases indCont_next h with ⟨-, g, mem', -, he, hm, -⟩ | ⟨-, -, n, g, rv, hg, hr⟩
  · rw [hm]; exact enterFunc_symbols he
  · exact hk _ _ hg _ _ _ _ hr

/-- A whole-program step keeps the symbols (when the externs do). -/
theorem step_symbols {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : Opt.EnvKeepsSymbols env) {s : State} (hI : LInv P s) :
    (∀ s1, step env P s = .next s1 → s1.mem.symbols = s.mem.symbols) ∧
    (∀ v m, step env P s = .done v m → m.symbols = s.mem.symbols) := by
  refine ⟨fun s1 h => ?_, fun v m h => ?_⟩
  · rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
      ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
    · rw [step_try env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      obtain ⟨⟨ext, vals⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      dsimp only at h
      exact callCont_symbols (t := tryState s bc) hk h
    · rw [step_tryInd env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      obtain ⟨⟨d, a, w⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      dsimp only at h
      exact indCont_symbols (t := tryState s bc) hk h
    · rw [step_ind env P s hb hi] at h
      obtain ⟨⟨d, a, w⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
      dsimp only at h
      exact indCont_symbols hk h
    · rw [Opt.step_eq_lift env P s hci] at h
      cases hl : Opt.lstep s.frame s.mem with
      | next fr1 m1 =>
        rw [hl] at h; cases h
        exact (Opt.lstep_next_frame hl).2.2
      | call ext vals rs rest => rw [hl] at h; exact callCont_symbols hk h
      | ret vals => rw [hl] at h; rw [returnValues_mem.1 s1 h, Mem.leave_symbols]; rfl
      | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
      | trap c => rw [hl] at h; cases h
      | stuck m => rw [hl] at h; cases h
  · rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
      ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
    · rw [step_try env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
      obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
      exact absurd h callCont_ne_done
    · rw [step_tryInd env P s hb ht] at h
      obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
      obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
      exact absurd h indCont_ne_done
    · rw [step_ind env P s hb hi] at h
      obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
      exact absurd h indCont_ne_done
    · rw [Opt.step_eq_lift env P s hci] at h
      cases hl : Opt.lstep s.frame s.mem with
      | ret vals => rw [hl] at h; rw [returnValues_mem.2 v m h, Mem.leave_symbols]; rfl
      | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
      | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
      | next fr1 m1 => rw [hl] at h; cases h
      | trap c => rw [hl] at h; cases h
      | stuck m => rw [hl] at h; cases h

/-- A returning whole-program run keeps the symbols (when the externs do). -/
theorem runLoop_symbols {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : Opt.EnvKeepsSymbols env) :
    ∀ (N : Nat) (s : State) (vals : List Val) (mem : Mem), LInv P s →
      runLoop env P N s = .returned vals mem → mem.symbols = s.mem.symbols
  | 0, _, _, _, _, h => by simp at h
  | N + 1, s, vals, mem, hI, h => by
    rw [runLoop_succ'] at h
    cases hs : step env P s with
    | next s1 =>
      rw [hs] at h
      rw [runLoop_symbols hP hk N s1 vals mem (step_next_linv hP hI hs).1 h,
        (step_symbols hP hk hI).1 s1 hs]
    | done v m =>
      rw [hs] at h
      simp only [afterStep, Outcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (step_symbols hP hk hI).2 v m hs
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

theorem initState_symbols {P : Program} {n : String} {vals : List Val} {mem : Mem} {s : State}
    (h : initState P n vals mem = .ok s) : s.mem.symbols = mem.symbols ∧ s.callers = [] ∧
      ∃ g, P.func? n = some g ∧ ∃ mem', enterFunc g vals mem = .ok (s.frame, mem') ∧ s.mem = mem' := by
  simp only [initState] at h
  cases hf : P.func? n with
  | none => rw [hf] at h; cases h
  | some g =>
    rw [hf] at h
    simp only [Res.ofOption_some, Res.ok_bind] at h
    cases he : enterFunc g vals mem with
    | ok r =>
      rw [he] at h
      obtain ⟨fr, mem'⟩ := r
      simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq] at h
      subst h
      exact ⟨enterFunc_symbols he, rfl, g, rfl, mem', he, rfl⟩
    | trap => rw [he] at h; cases h
    | stuck => rw [he] at h; cases h

/-- The linked environment keeps the symbols when the base one does. -/
theorem linkEnvN_keeps {P : Program} {base : Env} {M : Nat} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hk : Opt.EnvKeepsSymbols base) : Opt.EnvKeepsSymbols (linkEnvN P base M) := by
  intro n gsem hg vals m rvals m' hr
  cases hpf : P.func? n with
  | none => rw [linkEnvN_none hpf] at hg; exact hk n gsem hg vals m rvals m' hr
  | some g =>
    rw [linkEnvN_some hpf] at hg
    cases hg
    simp only at hr
    cases hi : initState P n vals m with
    | ok s =>
      rw [hi] at hr
      simp only at hr
      obtain ⟨hs, hc, g', hpf', mem', he, -⟩ := initState_symbols hi
      rw [hpf] at hpf'; cases hpf'
      have hI : LInv P s := ⟨LFrame.enterFunc (Program.func?_some hpf).1 he, by rw [hc]; exact fun _ h => nomatch h⟩
      rw [runLoop_symbols hP hk M s rvals m' hI hr, hs]
    | trap c => rw [hi] at hr; cases hr
    | stuck msg => rw [hi] at hr; cases hr

/-! ## Resolving an indirect call in the per-function program -/

theorem names_func {P : Program} {g : Function} (hg : g ∈ P.funcs) : g.name ∈ P.names :=
  List.mem_append_left _ (List.mem_map_of_mem hg)

theorem names_extern {P : Program} {n : String} (hn : n ∈ P.externNames) : n ∈ P.names :=
  List.mem_append_right _ hn

theorem externs_sub {P : Program} {f : Function} (hf : f ∈ P.funcs) :
    ∀ n ∈ f.externs.map (·.2.name), n ∈ P.externNames := fun n hn => by
  simp only [Program.externNames, List.mem_flatMap]
  exact ⟨f, hf, hn⟩

theorem only_externNames (P : Program) (f : Function) :
    (P.only f).externNames = f.externs.map (·.2.name) := by
  simp [Program.externNames, Program.only]

/-- Every name the per-function program of `f` resolves an indirect call through (the linked
environment's, then `f`'s declarations) is a name of `P` or of `base`. -/
theorem linkNames_sub {P : Program} {base : Env} {f : Function} {M : Nat} (hf : f ∈ P.funcs)
    {n : String} (hn : n ∈ (linkEnvN P base M).names ++ (P.only f).externNames) :
    n ∈ P.names ++ base.names := by
  rw [linkEnvN_names, only_externNames, List.mem_append] at hn
  rcases hn with hn | hn
  · exact hn
  · exact List.mem_append_left _ (names_extern (externs_sub hf n hn))

/-- `callExternAt` resolving the callee address to names with the same extern gives the same
result, up to the messages of a stuck call (they name the extern). -/
theorem callExternAt_alias {E₁ E₂ : Env} {p₁ p₂ : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} {n₁ n₂ : String}
    (h₁ : (E₁.names ++ p₁.externNames).find? (fun n => mem.symbols n == some a) = some n₁)
    (h₂ : (E₂.names ++ p₂.externNames).find? (fun n => mem.symbols n == some a) = some n₂)
    (he : E₁.extern n₁ = E₂.extern n₂) :
    callExternAt E₁ p₁ mem d a vals = callExternAt E₂ p₂ mem d a vals ∨
      ((∃ m, callExternAt E₁ p₁ mem d a vals = .stuck m) ∧
        ∃ m, callExternAt E₂ p₂ mem d a vals = .stuck m) := by
  unfold callExternAt
  rw [h₁, h₂]
  simp only [Res.ofOption_some, Res.ok_bind]
  rw [← he]
  cases E₁.extern n₁ with
  | none => exact .inr ⟨⟨_, rfl⟩, _, rfl⟩
  | some g =>
    simp only [Res.ofOption_some, Res.ok_bind, checkTys]
    cases (vals.map (·.ty) == AbiParam.tys d.params) with
    | false => exact .inr ⟨⟨_, rfl⟩, _, rfl⟩
    | true =>
      simp only [Res.check_true, Res.ok_bind]
      cases g vals mem with
      | returned rvals mem' =>
        dsimp only
        cases (List.map (fun x => x.ty) rvals == AbiParam.tys d.returns) with
        | false => exact .inr ⟨⟨_, rfl⟩, _, rfl⟩
        | true => exact .inl rfl
      | trapped c => exact .inl rfl
      | stuck m => exact .inl rfl
      | outOfFuel => exact .inr ⟨⟨_, rfl⟩, _, rfl⟩

/-- An indirect call to no function of `P` resolves, in the per-function program of `f`, to an
extern of `base` (the linked environment's names hold every name of `P` and of `base`) with the
whole program's semantics (`IndScope.alias`): the same result, up to the messages of a stuck
call. -/
theorem callExternAt_eq {P : Program} {base : Env} {f : Function} {syms : String → Option Nat}
    {M : Nat} (hf : f ∈ P.funcs) (hS : IndScope P base syms) {mem : Mem} (hm : mem.symbols = syms)
    {d : Signature} {a : Nat} {vals : List Val}
    (hnone : P.funcs.find? (fun g => mem.symbols g.name == some a) = none) :
    callExternAt (linkEnvN P base M) (P.only f) mem d a vals = callExternAt base P mem d a vals ∨
      ((∃ m, callExternAt (linkEnvN P base M) (P.only f) mem d a vals = .stuck m) ∧
        ∃ m, callExternAt base P mem d a vals = .stuck m) := by
  have hno : ∀ g ∈ P.funcs, mem.symbols g.name ≠ some a := fun g hg e => by
    have := List.find?_eq_none.mp hnone g hg
    simp [e] at this
  have hnp : ∀ n, mem.symbols n = some a → P.func? n = none := fun n hq => by
    cases e : P.func? n with
    | none => rfl
    | some g =>
      obtain ⟨hg, rfl⟩ := Program.func?_some e
      exact absurd hq (hno g hg)
  have hsub : ∀ n, mem.symbols n = some a →
      n ∈ (linkEnvN P base M).names ++ (P.only f).externNames → n ∈ base.names ++ P.externNames :=
    fun n hq hn => by
      rcases List.mem_append.mp (linkNames_sub hf hn) with hn | hn
      · rcases List.mem_append.mp hn with hn | hn
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
          exact absurd hq (hno g hg)
        · exact List.mem_append_right _ hn
      · exact List.mem_append_left _ hn
  have hsup : ∀ n, n ∈ base.names ++ P.externNames →
      n ∈ (linkEnvN P base M).names ++ (P.only f).externNames := fun n hn => by
    rw [linkEnvN_names, List.append_assoc, List.mem_append]
    rcases List.mem_append.mp hn with hn | hn
    · exact .inr (List.mem_append_left _ hn)
    · exact .inl (names_extern hn)
  cases h₂ : (base.names ++ P.externNames).find? (fun n => mem.symbols n == some a) with
  | none =>
    have h₁ : ((linkEnvN P base M).names ++ (P.only f).externNames).find?
        (fun n => mem.symbols n == some a) = none := by
      rw [List.find?_eq_none] at h₂ ⊢
      intro n hn hq
      exact h₂ n (hsub n (by simpa using hq) hn) hq
    left
    unfold callExternAt
    rw [h₁, h₂]
    rfl
  | some n₂ =>
    have hq₂ : mem.symbols n₂ = some a := by simpa using List.find?_some h₂
    have hm₂ := List.mem_of_find?_eq_some h₂
    cases h₁ : ((linkEnvN P base M).names ++ (P.only f).externNames).find?
        (fun n => mem.symbols n == some a) with
    | none => exact absurd (List.find?_eq_none.mp h₁ n₂ (hsup n₂ hm₂)) (by simp [hq₂])
    | some n₁ =>
      have hq₁ : mem.symbols n₁ = some a := by simpa using List.find?_some h₁
      have hm₁ := List.mem_of_find?_eq_some h₁
      have hp₁ := hnp n₁ hq₁
      have hp₂ := hnp n₂ hq₂
      refine callExternAt_alias h₁ h₂ ?_
      rw [linkEnvN_none hp₁]
      have hn₂ : n₂ ∈ P.names ++ base.names := by
        rcases List.mem_append.mp hm₂ with h | h
        · exact List.mem_append_right _ h
        · exact List.mem_append_left _ (names_extern h)
      rw [hm] at hq₁ hq₂
      exact hS.alias n₁ (linkNames_sub hf hm₁) n₂ hn₂ a hq₁ hq₂ hp₁ hp₂

/-- The name of an extern a function declares is a name of its declarations. -/
theorem lookup_name_mem : ∀ {l : List (FnRef × ExtFunc)} {fn : FnRef} {e : ExtFunc},
    l.lookup fn = some e → e.name ∈ l.map (·.2.name)
  | [], _, _, h => by simp at h
  | (x, y) :: l, fn, e, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lookup_name_mem h)

/-- `callExternAt` under environments with the same names and the same externs at the names
with the callee address. -/
theorem callExternAt_congr {E₁ E₂ : Env} {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} (hn : E₁.names = E₂.names)
    (hx : ∀ n, mem.symbols n = some a → E₁.extern n = E₂.extern n) :
    callExternAt E₁ p mem d a vals = callExternAt E₂ p mem d a vals := by
  unfold callExternAt
  rw [hn]
  cases hf : (E₂.names ++ p.externNames).find? (fun n => mem.symbols n == some a) with
  | none => rfl
  | some n =>
    have hq : mem.symbols n = some a := by simpa using List.find?_some hf
    simp only [Res.ofOption_some, Res.ok_bind, hx n hq]

/-- **Linking at the CLIF level with bounded callee runs** (`runLoop_link` with
`linkEnvN P base M`): a complete whole-program run of at most `M + 1` steps is a complete
per-function run whose program callees run at most `M` steps. The run's frames are `f`'s in the
per-function program (`LInv (P.only f)`); an indirect call of `f` (`call_indirect`,
`try_call_indirect`) resolves, in the per-function program, through the linked environment's
names (`IndScope`, with the memory's symbols `syms`), whatever `f` declares. The per-function
environment `E` may be `linkEnvN P base M` without the functions of `P` that the whole-program
run of `f` cannot call (`hEp`): those `f` neither declares nor can enter through one of its
indirect calls, whose call-site signature (`IndSig`) must match the callee's
(`Signature.abiMatch`, checked by `Clif.stepCallIndirect`). -/
theorem runLoop_linkN {P : Program} {base : Env} {f : Function} {syms : String → Option Nat}
    (M : Nat) (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hio : ¬ IndFree f → IndScope P base syms) {E : Env}
    (hEn : E.names = (linkEnvN P base M).names)
    (hEb : ∀ n, P.func? n = none → E.extern n = (linkEnvN P base M).extern n)
    (hEp : ∀ h ∈ P.funcs, h.name ≠ f.name → (h.name ∈ f.externs.map (·.2.name) ∨
      (syms h.name ≠ none ∧ ∃ d, IndSig f d ∧ d.abiMatch h.sig = true)) →
      E.extern h.name = (linkEnvN P base M).extern h.name) :
    ∀ (N : Nat) (s : State), N ≤ M + 1 → LInv P s → LInv (P.only f) s →
      (¬ IndFree f → s.mem.symbols = syms) →
      (∀ msg, runLoop base P N s ≠ .stuck msg) → runLoop base P N s ≠ .outOfFuel →
      ∃ m, runLoop E (P.only f) m s = runLoop base P N s := by
  have hPf : ∀ g ∈ (P.only f).funcs, LinkFree g := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hP g hf
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro s hNM hI hIf hsy hst hof
  cases N with
  | zero => exact absurd rfl hof
  | succ N =>
  -- a per-function step `r` after which the whole-program run continues with `n` steps
  have helper : ∀ (r : StepResult) (n : Nat), n < N + 1 →
      step E (P.only f) s = r → runLoop base P (N + 1) s = afterStep base P n r →
      (∀ s1, r = .next s1 → LInv P s1 ∧ LInv (P.only f) s1 ∧ (¬ IndFree f → s1.mem.symbols = syms)) →
      ∃ m, runLoop E (P.only f) m s = runLoop base P (N + 1) s := by
    intro r n hn hr hrun hinv
    cases r with
    | next s1 =>
      rw [hrun] at hst hof ⊢
      obtain ⟨h1, h2, h3⟩ := hinv s1 rfl
      obtain ⟨m, hm⟩ := ih n hn s1 (by omega) h1 h2 h3 hst hof
      exact ⟨m + 1, by rw [runLoop_succ', hr]; exact hm⟩
    | _ => exact ⟨0 + 1, by rw [runLoop_succ', hr, hrun]; rfl⟩
  -- the steps that do not call another function of `P` are the same
  have same : step E (P.only f) s = step base P s →
      ∃ m, runLoop E (P.only f) m s = runLoop base P (N + 1) s := fun h =>
    helper _ N (by omega) h (runLoop_succ' ..) fun s1 hs1 =>
      ⟨(step_next_linv hP hI hs1).1, (step_next_linv hPf hIf (h.trans hs1)).1,
        fun hn => ((step_symbols hP (hio hn).keep hI).1 s1 hs1).trans (hsy hn)⟩
  -- an atomic call of `g` from `t` (whose frame is `s`'s up to `regs`/`body`/`term`): the
  -- whole-program step enters `g`, the per-function step runs `g`'s whole-program run
  have atomic : ∀ (t : State) rest rs (g : Function) vals, g ∈ P.funcs → t.callers = s.callers →
      (∀ regs, LFrame P { t.frame with regs, body := rest } ∧
        LFrame (P.only f) { t.frame with regs, body := rest }) →
      (¬ IndFree f → t.mem.symbols = syms) →
      step base P s = StepResult.ofRes (enterFunc g vals t.mem) (fun (fr', mem') =>
        .next { frame := fr',
                callers := ({ t.frame with body := rest }, rs) :: t.callers,
                mem := mem' }) →
      (∀ fr' mem', enterFunc g vals t.mem = .ok (fr', mem') →
        (∀ rvals mem2, runLoop base P M ⟨fr', [], mem'⟩ = .returned rvals mem2 →
          rvals.map (·.ty) = AbiParam.tys g.sig.returns →
          step E (P.only f) s = continueWith t rest rs rvals mem2) ∧
        (∀ c, runLoop base P M ⟨fr', [], mem'⟩ = .trapped c →
          step E (P.only f) s = .trapped c)) →
      ∃ m, runLoop E (P.only f) m s = runLoop base P (N + 1) s := by
    intro t rest rs g vals hgP htc hfr htsy e1 e2
    rw [runLoop_succ', e1] at hst hof
    rw [runLoop_succ', e1]
    cases he : enterFunc g vals t.mem with
    | trap c => exact absurd he (Opt.enterFunc_not_trap g vals t.mem c)
    | stuck m =>
      rw [he] at hst; exact absurd rfl (hst m)
    | ok a =>
      obtain ⟨fr', mem'⟩ := a
      obtain ⟨e2r, e2t⟩ := e2 fr' mem' he
      rw [he] at hst hof
      simp only [StepResult.ofRes_ok, afterStep] at hst hof ⊢
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
        have e2' := e2r rvals mem2 hlim hty
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
            ⟨(hfr regs).1, by rw [htc]; exact hI.2⟩ ⟨(hfr regs).2, by rw [htc]; exact hIf.2⟩
            (fun hn => by
              show mem2.symbols = syms
              rw [runLoop_symbols hP (hio hn).keep N _ rvals mem2 hsubI hsub]
              show mem'.symbols = syms
              rw [enterFunc_symbols he, htsy hn]) hst hof
          exact ⟨m + 1, by rw [runLoop_succ', e2']; exact hm⟩
      | trapped c =>
        have hne : ∀ vals mem, runLoop base P N ⟨fr', [], mem'⟩ ≠ .returned vals mem := by
          rw [hsub]; exact fun _ _ h => by cases h
        rw [runLoop_below_of_not_returned base P K N _ hne, hsub] at hst hof ⊢
        have hlim : runLoop base P M ⟨fr', [], mem'⟩ = .trapped c := by
          rw [show M = N + (M - N) by omega,
            runLoop_add base P N _ (by rw [hsub]; exact fun h => by cases h)]
          exact hsub
        exact ⟨1, by rw [runLoop_succ', e2t c hlim]; rfl⟩
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
  -- a call (`callCont`) from `t`
  have call : ∀ (t : State) rest rs ext vals, t.callers = s.callers → t.mem = s.mem →
      (∀ regs, LFrame P { t.frame with regs, body := rest } ∧
        LFrame (P.only f) { t.frame with regs, body := rest }) →
      ext.name ∈ f.externs.map (·.2.name) →
      step base P s = Opt.callCont base P t rest rs ext vals →
      step E (P.only f) s = Opt.callCont E (P.only f) t rest rs ext vals →
      ∃ m, runLoop E (P.only f) m s = runLoop base P (N + 1) s := by
    intro t rest rs ext vals htc htm hfr hext e1 e2
    cases hpf : P.func? ext.name with
    | none =>
      have hfn : f.name ≠ ext.name := Program.func?_none hpf f hf
      apply same
      rw [e1, e2]
      simp only [Opt.callCont, hpf, Program.only_func?, hfn, ↓reduceIte, hEb _ hpf,
        linkEnvN_none hpf]
    | some g =>
      obtain ⟨hgP, hgn⟩ := Program.func?_some hpf
      by_cases hgf : g = f
      · subst hgf
        apply same
        rw [e1, e2]
        simp only [Opt.callCont, hpf, Program.only_func?, hgn, ↓reduceIte]
      have hfn : f.name ≠ ext.name := fun h => hgf (name_inj hnd hgP hf (hgn.trans h.symm))
      have hEg : E.extern ext.name = (linkEnvN P base M).extern ext.name := by
        rw [← hgn]
        exact hEp g hgP (fun h => hfn (h.symm.trans hgn)) (.inl (by rw [hgn]; exact hext))
      have e2' := e2
      simp only [Opt.callCont, Program.only_func?, hfn, ↓reduceIte, hEg, linkEnvN_some hpf] at e2'
      cases hsig : (AbiParam.tys g.sig.params == AbiParam.tys ext.sig.params &&
          AbiParam.tys g.sig.returns == AbiParam.tys ext.sig.returns) with
      | false =>
        rw [runLoop_succ', e1] at hst
        simp only [Opt.callCont, hpf, hsig, Bool.false_eq_true, ↓reduceIte, afterStep] at hst
        exact absurd rfl (hst _)
      | true =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hsig
        refine atomic t rest rs g vals hgP htc hfr (fun hn => htm ▸ hsy hn)
          (by rw [e1]; simp only [Opt.callCont, hpf, hsig, beq_self_eq_true, Bool.and_self, ↓reduceIte])
          fun fr' mem' he => ⟨fun rvals mem2 hlim hty => ?_, fun c hlim => ?_⟩
        · have hinit : initState P ext.name vals t.mem = .ok ⟨fr', [], mem'⟩ := by
            simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
          rw [e2', hinit]
          simp only [hlim, hty, hsig.2, beq_self_eq_true, ↓reduceIte]
        · have hinit : initState P ext.name vals t.mem = .ok ⟨fr', [], mem'⟩ := by
            simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
          rw [e2', hinit]
          simp only [hlim]
  -- an indirect call (`indCont`) from `t`, a frame of `f`
  have ind : ∀ (t : State) rest rs sig d a v, t.callers = s.callers → t.mem = s.mem →
      (∀ regs, LFrame P { t.frame with regs, body := rest } ∧
        LFrame (P.only f) { t.frame with regs, body := rest }) → IndSig f d →
      step base P s = indCont base P t rest rs sig d a v →
      step E (P.only f) s = indCont E (P.only f) t rest rs sig d a v →
      ∃ m, runLoop E (P.only f) m s = runLoop base P (N + 1) s := by
    intro t rest rs sig d a v htc htm hfr hdS e1 e2
    have hnf : ¬ IndFree f := hdS.not_indFree
    have hS := hio hnf
    have hm : t.mem.symbols = syms := htm ▸ hsy hnf
    cases hfind : P.funcs.find? (fun g => t.mem.symbols g.name == some a) with
    | none =>
      have h1 : (P.only f).funcs.find? (fun g => t.mem.symbols g.name == some a) = none := by
        simp only [Program.only, List.find?_cons, List.find?_nil]
        have := List.find?_eq_none.mp hfind f hf
        simp only [this]
      have hcg : callExternAt E (P.only f) t.mem d a v =
          callExternAt (linkEnvN P base M) (P.only f) t.mem d a v := by
        refine callExternAt_congr hEn fun n hq => hEb n ?_
        cases e : P.func? n with
        | none => rfl
        | some g =>
          obtain ⟨hg, rfl⟩ := Program.func?_some e
          have := List.find?_eq_none.mp hfind g hg
          simp [hq] at this
      rcases callExternAt_eq (M := M) (d := d) (vals := v) hf hS hm hfind with he | ⟨-, m₂, h₂⟩
      · apply same
        rw [e1, e2]
        simp only [indCont, hfind, h1, hcg, he]
      · rw [runLoop_succ', e1] at hst
        simp only [indCont, hfind, h₂, StepResult.ofRes_stuck, afterStep] at hst
        exact absurd rfl (hst _)
    | some h =>
      have hhP := List.mem_of_find?_eq_some hfind
      have hha : t.mem.symbols h.name = some a := by simpa using List.find?_some hfind
      by_cases hhf : h = f
      · subst hhf
        have h1 : (P.only h).funcs.find? (fun g => t.mem.symbols g.name == some a) = some h := by
          simp [Program.only, hha]
        apply same
        rw [e1, e2]
        simp only [indCont, hfind, h1]
      have h1 : (P.only f).funcs.find? (fun g => t.mem.symbols g.name == some a) = none := by
        simp only [Program.only, List.find?_cons, List.find?_nil]
        cases e : (t.mem.symbols f.name == some a) with
        | false => rfl
        | true =>
          simp only [beq_iff_eq] at e
          rw [hm] at e hha
          exact absurd (name_inj hnd hf hhP
            (hS.inj f.name (List.mem_map_of_mem hf) h.name (List.mem_map_of_mem hhP) a e hha)).symm
            hhf
      -- the per-function program resolves the address to `h` (the first function of `P` there,
      -- the first names of the linked environment)
      have hname : (E.names ++ (P.only f).externNames).find?
          (fun n => t.mem.symbols n == some a) = some h.name := by
        simp only [hEn, linkEnvN_names, Program.names, List.append_assoc, List.find?_append,
          List.find?_map, Function.comp_def, hfind, Option.map_some, Option.some_or]
      have hpf : P.func? h.name = some h := by
        cases e : P.func? h.name with
        | none => exact absurd rfl (Program.func?_none e h hhP)
        | some g =>
          obtain ⟨hg, hgn⟩ := Program.func?_some e
          rw [name_inj hnd hg hhP hgn]
      cases hsig : d.abiMatch h.sig with
      | false =>
        rw [runLoop_succ', e1] at hst
        simp only [indCont, hfind, hsig, Bool.false_eq_true, ↓reduceIte, afterStep] at hst
        exact absurd rfl (hst _)
      | true =>
        have hsig' := Signature.abiMatch_eq_true.mp hsig
        have hEh : E.extern h.name = (linkEnvN P base M).extern h.name :=
          hEp h hhP (fun e => hhf (name_inj hnd hhP hf e))
            (.inr ⟨by rw [← hm, hha]; exact Option.some_ne_none a, d, hdS, hsig⟩)
        refine atomic t rest rs h v hhP htc hfr (fun _ => hm)
          (by rw [e1]; simp only [indCont, hfind, hsig, ↓reduceIte])
          fun fr' mem' he => ?_
        have hinit : initState P h.name v t.mem = .ok ⟨fr', [], mem'⟩ := by
          simp [initState, hpf, he, Res.ofOption, bind, Res.bind, pure]
        have hvt : v.map (·.ty) = AbiParam.tys d.params := by
          obtain ⟨_, _, _, h1, -⟩ := Opt.enterFunc_ok he
          rw [h1, hsig'.1]
        refine ⟨fun rvals mem2 hlim hty => ?_, fun c hlim => ?_⟩
        · rw [e2]
          simp only [indCont, h1, callExternAt, hname, Res.ofOption_some, Res.ok_bind, hEh,
            linkEnvN_some hpf, checkTys, hvt, beq_self_eq_true, Res.check_true, hinit, hlim, hty,
            hsig'.2.2, ↓reduceIte, Res.pure_eq, StepResult.ofRes_ok]
        · rw [e2]
          simp only [indCont, h1, callExternAt, hname, Res.ofOption_some, Res.ok_bind, hEh,
            linkEnvN_some hpf, checkTys, hvt, beq_self_eq_true, Res.check_true, hinit, hlim,
            StepResult.ofRes_trap]
  have hff : s.frame.func = f := by
    have := hIf.1.1
    simpa [Program.only] using this
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · -- a `try_call`: its preludes are the same, then the call from the waiting frame
    have e1 := step_try base P s hb ht
    have e2 := step_try E (P.only f) s hb ht
    rcases ofRes_cases (tryPre s.frame fn et) _ _ with h1 | ⟨⟨n, b, bc⟩, -, h1, h1'⟩
    · exact same (by rw [e1, e2]; exact h1.symm)
    rw [h1] at e1
    rw [h1'] at e2
    dsimp only at e1 e2
    rcases ofRes_cases (Opt.callArgs (tryState s bc).frame fn args) _ _ with h2 | ⟨⟨ext, vals⟩, hX, h2, h2'⟩
    · exact same (by rw [e1, e2]; exact h2.symm)
    rw [h2] at e1
    rw [h2'] at e2
    dsimp only at e1 e2
    have hext : f.extern? fn = some ext := by
      have := Opt.callArgs_extern hX; rw [← hff]; exact this
    exact call (tryState s bc) [] _ ext vals rfl rfl
      (fun regs => ⟨LFrame.jump hI.1.1 regs bc, LFrame.jump hIf.1.1 regs bc⟩)
      (lookup_name_mem hext) e1 e2
  · -- a `try_call_indirect`
    have e1 := step_tryInd base P s hb ht
    have e2 := step_tryInd E (P.only f) s hb ht
    rcases ofRes_cases (tryIndPre s.frame et) _ _ with h1 | ⟨⟨n, b, bc⟩, -, h1, h1'⟩
    · exact same (by rw [e1, e2]; exact h1.symm)
    rw [h1] at e1
    rw [h1'] at e2
    dsimp only at e1 e2
    rcases ofRes_cases (indPre (tryState s bc).frame et.sig callee args) _ _ with
      h2 | ⟨⟨d, a, v⟩, hX, h2, h2'⟩
    · exact same (by rw [e1, e2]; exact h2.symm)
    rw [h2] at e1
    rw [h2'] at e2
    dsimp only at e1 e2
    have hdS : IndSig f d := by
      have hl := indPre_lookup hX
      rcases hIf.1 with ⟨-, ⟨b0, hb0, -, ht0⟩ | ⟨-, bc0, ht0⟩⟩
      · rw [hff] at hb0
        refine ⟨b0, hb0, .inr ⟨callee, args, et, ht0.symm.trans ht, ?_⟩⟩
        rw [← hff]; exact hl
      · rw [ht] at ht0; cases ht0
    exact ind (tryState s bc) [] _ et.sig d a v rfl rfl
      (fun regs => ⟨LFrame.jump hI.1.1 regs bc, LFrame.jump hIf.1.1 regs bc⟩) hdS e1 e2
  · -- a `call_indirect` statement
    have e1 := step_ind base P s hb hi
    have e2 := step_ind E (P.only f) s hb hi
    rcases ofRes_cases (indPre s.frame sig callee args) _ _ with h1 | ⟨⟨d, a, v⟩, hX, h1, h1'⟩
    · exact same (by rw [e1, e2]; exact h1.symm)
    rw [h1] at e1
    rw [h1'] at e2
    dsimp only at e1 e2
    have hdS : IndSig f d := by
      have hl := indPre_lookup hX
      rcases hIf.1 with ⟨-, ⟨b0, hb0, hsuf, -⟩ | ⟨hnil, -⟩⟩
      · rw [hff] at hb0
        refine ⟨b0, hb0, .inl ⟨st, hsuf.subset (by rw [hb]; simp), sig, callee, args, hi, ?_⟩⟩
        rw [← hff]; exact hl
      · rw [hnil] at hb; cases hb
    exact ind s rest st.results sig d a v rfl rfl
      (fun regs => ⟨hI.1.rest hb regs, hIf.1.rest hb regs⟩) hdS e1 e2
  · have e1 := Opt.step_eq_lift base P s hci
    have e2 := Opt.step_eq_lift E (P.only f) s hci
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 => exact same (by rw [e1, e2, hl]; rfl)
    | ret vals => exact same (by rw [e1, e2, hl]; rfl)
    | trap c => exact same (by rw [e1, e2, hl]; rfl)
    | stuck m => exact same (by rw [e1, e2, hl]; rfl)
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1)
    | call ext vals rs rest =>
      rw [hl] at e1 e2
      obtain ⟨st, fn, args, hb, -, -, hca⟩ := Opt.lstep_call_inv hl
      have hext : f.extern? fn = some ext := by rw [← hff]; exact Opt.callArgs_extern hca
      exact call s rest rs ext vals rfl rfl (fun regs => ⟨hI.1.rest hb regs, hIf.1.rest hb regs⟩)
        (lookup_name_mem hext) e1 e2


end Clif
