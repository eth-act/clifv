module

public import FV.E2E.TrapCallClif

@[expose] public section

/-!
# Callee traps: the premise and the run with unwinding of `trapEnv` (S9a, #33)

`TrapsExplicitC` (the widened run premise), and for a run of a function without
`try_call`/`return_call` terminators that traps with `c`: `TrapsExplicitX` of `trapEnv env c`
(`trapsExplicitX_trapEnv`) and its run with unwinding, which traps with `c` or ends with an
exception (`runLoopX_trapEnv`, `trapEnv_of_trapped`).
-/

namespace E2E

open Clif Backend.Proof Backend.Proof.Driver

section
variable {env : Env} {c : TrapCode} {p : Program}

/-! ## Preludes never trap -/

theorem getMany_ne_trap (fr : Frame) : ∀ (xs : List ValueId) (c' : TrapCode), fr.getMany xs ≠ .trap c'
  | [], _ => by simp [Frame.getMany]
  | x :: xs, _ => by
    simp only [Frame.getMany, Frame.get]
    cases fr.regs x with
    | none => simp
    | some v =>
      simp only [Res.ofOption_some, Res.ok_bind]
      cases h : fr.getMany xs with
      | ok vs => simp
      | trap c'' => exact absurd h (getMany_ne_trap fr xs c'')
      | stuck m => simp

theorem callArgs_ne_trap (fr : Frame) (fn : FnRef) (args : List ValueId) :
    Opt.callArgs fr fn args ≠ .trap c := by
  unfold Opt.callArgs
  cases fr.func.extern? fn with
  | none => simp
  | some ext =>
    simp only [Res.ofOption_some, Res.ok_bind]
    have h := getMany_ne_trap fr args
    cases hg : fr.getMany args with
    | ok vals =>
      simp only [Res.ok_bind, checkTys, Res.check]
      split <;> simp
    | trap c' => exact absurd hg (h c')
    | stuck m => simp

theorem indPre_ne_trap (fr : Frame) (sig : Nat) (callee : ValueId) (args : List ValueId) :
    indPre fr sig callee args ≠ .trap c := by
  unfold indPre
  cases fr.func.sigDecls.lookup sig with
  | none => simp
  | some d =>
    simp only [Res.ofOption_some, Res.ok_bind, Frame.get]
    cases fr.regs callee with
    | none => simp
    | some cv =>
      simp only [Res.ofOption_some, Res.ok_bind]
      cases cv.as? .i64 with
      | none => simp
      | some x =>
        simp only [Res.ofOption_some, Res.ok_bind]
        have h := getMany_ne_trap fr args
        cases hg : fr.getMany args with
        | ok vals => simp
        | trap c' => exact absurd hg (h c')
        | stuck m => simp

/-- **A call statement that traps with `c` in `env` does not trap with `c` in `trapEnv`'s
environment** (its callee trapped; there it is `stuck`). -/
theorem step_call_trap_stuck (env : Env) (c : TrapCode) (hp : p.funcs = []) {s : State}
    {st : Stmt} {rest : List Stmt} (hb : s.frame.body = st :: rest)
    (hi : (∃ fn args, st.inst = .call fn args) ∨ ∃ sig callee args, st.inst = .callIndirect sig callee args)
    (h : step env p s = .trapped c) : step (trapEnv env c).toEnv p s ≠ .trapped c := by
  intro h2
  rcases hi with ⟨fn, args, hi⟩ | ⟨sig, callee, args, hi⟩
  · rw [step_call env p s rest st.results fn args (by rw [hb, ← hi])] at h
    rw [step_call _ p s rest st.results fn args (by rw [hb, ← hi])] at h2
    have hca : ∀ E : Env, stepCall E p s rest st.results fn args =
        StepResult.ofRes (Opt.callArgs s.frame fn args) fun (ext, vals) =>
          Opt.callCont E p s rest st.results ext vals := fun _ => rfl
    rw [hca] at h h2
    cases ha : Opt.callArgs s.frame fn args with
    | ok r =>
      obtain ⟨ext, vals⟩ := r
      rw [ha] at h h2
      simp only [StepResult.ofRes] at h h2
      obtain ⟨g, he, hg⟩ := callCont_trap_inv hp h
      simp only [Opt.callCont, func?_nil hp, trapEnv_toEnv_extern, he, Option.map, hg,
        trapOut_self, XOutcome.toOutcome] at h2
      cases h2
    | trap c' => exact callArgs_ne_trap s.frame fn args ha
    | stuck m => rw [ha] at h; cases h
  · rw [step_ind _ _ s hb hi] at h h2
    cases ha : indPre s.frame sig callee args with
    | ok r =>
      obtain ⟨d, a, v⟩ := r
      rw [ha] at h h2
      simp only [StepResult.ofRes] at h h2
      have hx := indCont_trap_inv hp h
      obtain ⟨name, g, hf, he, hs, ht, hg⟩ := callExternAt_trap_inv hx
      simp only [indCont, find?_nil hp] at h2
      have hx2 : callExternAt (trapEnv env c).toEnv p s.mem d a v =
          .stuck "callee unwound (Clif.run has no unwinding)" := by
        unfold callExternAt
        have hn : (trapEnv env c).toEnv.names = env.names := rfl
        have hs' : (trapEnv env c).toEnv.sigOf = env.sigOf := rfl
        rw [hn, hs', hf]
        simp only [Res.ofOption_some, Res.ok_bind, trapEnv_toEnv_extern, he, Option.map, hs,
          Res.check_true, checkTys, ht, beq_self_eq_true, hg, trapOut_self, XOutcome.toOutcome]
      rw [hx2] at h2
      cases h2
    | trap c' => exact indPre_ne_trap s.frame sig callee args ha
    | stuck m => rw [ha] at h; cases h

/-! ## The premise -/

/-- A `call` or `call_indirect` instruction (whose step traps only inside its callee). -/
def CallInst (i : Inst) : Prop :=
  (∃ fn args, i = .call fn args) ∨ ∃ sig callee args, i = .callIndirect sig callee args

/-- **The run premises with callee traps** (`TrapsExplicit` widened): a statement traps only if
it is an explicitly trapping instruction **or a call whose callee trapped** (`CallInst`); the
other clauses are `TrapsExplicit`'s. Still excluded: memory-access traps (`heap_oob` of a
load/store: the Arm model has no memory faults) and traps of the callees of `try_call`s. -/
structure TrapsExplicitC (env : Env) (p : Program) (cs : State) : Prop where
  stmt : ∀ s c st rest, Reach env p cs s → step env p s = .trapped c →
    s.frame.body = st :: rest → explicitTrapInst st.inst = true ∨ CallInst st.inst
  tryCall : ∀ s c fn args et, Reach env p cs s → step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCall fn args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCall fn args et
  tryCallInd : ∀ s c callee args et, Reach env p cs s → step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCallIndirect callee args et →
    ∀ B ∈ cs.frame.func.blocks, B.term ≠ .tryCallIndirect callee args et
  indirect : ∀ s st rest sig callee args, Reach env p cs s → s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ cs.frame.func.blocks, st ∈ B.body) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat
  tryIndirect : ∀ s callee args et, Reach env p cs s → s.frame.body = [] →
    s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ cs.frame.func.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat

/-- `TrapsExplicit` is the special case without callee traps. -/
theorem TrapsExplicit.toC {cs : State} (h : TrapsExplicit env p cs) : TrapsExplicitC env p cs :=
  ⟨fun s c st rest hr hs hb => .inl (h.stmt s c st rest hr hs hb), h.tryCall, h.tryCallInd,
    h.indirect, h.tryIndirect⟩

/-! ## The activation's states -/

theorem bare_self (hp : p.funcs = []) : p.bare = p := by
  unfold Program.bare
  rw [← hp]

theorem linv_entry {f : Function} {args : List Val} {cs : State} (hcs : ClifEntry f args cs) :
    LInv (p.only f) cs := by
  obtain ⟨b, hb, hbody, hterm, -, -⟩ := hcs.entry
  refine ⟨⟨by rw [hcs.func]; simp [Program.only], .inl ⟨b, ?_, ?_, hterm⟩⟩, ?_⟩
  · rw [hcs.func]; exact List.mem_of_mem_head? hb
  · rw [hbody]; exact List.suffix_refl _
  · rw [hcs.callers]; simp

/-- In a frame of a function without `try_call` terminators, no step is at one. -/
theorem noTry_of_lframe {f : Function} (hf : ∀ B ∈ f.blocks, B.term.isTry = false) {fr : Frame}
    (h : LFrame (p.only f) fr) : fr.body = [] → fr.term.isTry = false := by
  intro _
  obtain ⟨hfm, ⟨b, hbm, -, ht⟩ | ⟨-, bc, ht⟩⟩ := h
  · have hff : fr.func = f := by simpa [Program.only] using hfm
    rw [hff] at hbm
    rw [ht]; exact hf b hbm
  · rw [ht]; rfl

theorem pendingOf_none {s : State} (h : s.frame.body = [] → s.frame.term.isTry = false) :
    pendingOf s = none := by
  unfold pendingOf
  cases hb : s.frame.body with
  | cons _ _ => rfl
  | nil =>
    have ht := h hb
    cases hterm : s.frame.term <;> rw [hterm] at ht <;> first | rfl | cases ht

/-- The run with unwinding of a state without callers whose step raises ends with the
exception (no `try_call` is pending). -/
theorem stepX_raise {env' : XEnv} {s : State} (hcl : s.callers = []) (hnp : pendingOf s = none)
    {e : Exn} {m : Mem} (hr : raiseAt? env' p s = some (e, m)) :
    ∃ m', stepX env' p ⟨s, []⟩ = .unwound e m' := by
  unfold stepX
  rw [hr]
  simp only [raiseIn, hnp, Option.bind_none, hcl, unwindFrom]
  exact ⟨_, rfl⟩

theorem liftStep_next {s s' : State} (hcl : s.callers = []) (hcl' : s'.callers = []) :
    liftStep ⟨s, []⟩ (.next s') = .next ⟨s', []⟩ := by
  simp [liftStep, hcl, hcl']

variable {f : Function}

theorem linkFree_only (hlf : LinkFree f) : ∀ g ∈ (p.only f).funcs, LinkFree g := by
  intro g hg
  simp only [Program.only, List.mem_singleton] at hg
  subst hg
  exact hlf

/-- **The run with unwinding of `trapEnv` reaches only states of `env`'s run**, without callers
and pending tables, in `f`'s frame. -/
theorem reachX_trapEnv (env : Env) (c : TrapCode) (hp : p.funcs = [])
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) (hlf : LinkFree f) {xs0 xs : XState}
    (h : ReachX (trapEnv env c) p xs0 xs) :
    ∀ s, xs0 = ⟨s, []⟩ → LInv (p.only f) s → s.callers = [] →
      xs.tries = [] ∧ Reach env p s xs.s ∧ LInv (p.only f) xs.s ∧ xs.s.callers = [] := by
  induction h with
  | refl xs =>
    intro s hx hI hcl
    subst hx
    exact ⟨rfl, .refl _, hI, hcl⟩
  | @step xs1 xs' xs'' hs _ ih =>
    intro s hx hI hcl
    subst hx
    have hnp := pendingOf_none (noTry_of_lframe hf hI.1)
    cases hr : raiseAt? (trapEnv env c) p s with
    | some em =>
      obtain ⟨e, m⟩ := em
      obtain ⟨m', hm⟩ := stepX_raise hcl hnp hr
      rw [hm] at hs; cases hs
    | none =>
      have hsx : stepX (trapEnv env c) p ⟨s, []⟩ =
          liftStep ⟨s, []⟩ (step (trapEnv env c).toEnv p s) := by
        unfold stepX; rw [hr]
      rw [hsx] at hs
      cases hst : step (trapEnv env c).toEnv p s with
      | next s' =>
        have hse : step env p s = .next s' := by
          rcases step_trapRel env c hp s with e | ⟨-, m, e⟩
          · rw [← e, hst]
          · rw [hst] at e; cases e
        have hI' := (step_next_linv (linkFree_only hlf) hI hse
          (fun g hg => by simp [hp] at hg)).1
        have hcl' : s'.callers = [] :=
          step_bare_callers (linkFree_only hlf) hI.1 hcl (by rw [bare_self hp]; exact hse)
        rw [hst, liftStep_next hcl hcl'] at hs
        cases hs
        obtain ⟨h1, h2, h3, h4⟩ := ih s' rfl hI' hcl'
        exact ⟨h1, .step hse h2, h3, h4⟩
      | done v m => rw [hst] at hs; simp [liftStep] at hs
      | trapped c' => rw [hst] at hs; simp [liftStep] at hs
      | stuck m => rw [hst] at hs; simp [liftStep] at hs

/-- A trapping step reachable from `s` is the trap of `s`'s run. -/
theorem reach_trapped_runLoop {s s1 : State} (h : Reach env p s s1) {c' : TrapCode}
    (hs : step env p s1 = .trapped c') : ∃ n, runLoop env p (n + 1) s = .trapped c' := by
  induction h with
  | refl => exact ⟨0, by rw [runLoop_succ, hs]⟩
  | step h1 _ ih =>
    obtain ⟨n, hn⟩ := ih hs
    exact ⟨n + 1, by rw [runLoop_succ, h1]; exact hn⟩

theorem trapped_det {s : State} {n m : Nat} {c₁ c₂ : TrapCode}
    (h1 : runLoop env p n s = .trapped c₁) (h2 : runLoop env p m s = .trapped c₂) : c₁ = c₂ := by
  have e1 := runLoop_add env p n s (by rw [h1]; simp) m
  have e2 := runLoop_add env p m s (by rw [h2]; simp) n
  rw [Nat.add_comm, e2, h2, h1] at e1
  cases e1; rfl

/-- **`TrapsExplicitX` of `trapEnv env c`** from `TrapsExplicitC` of a run of `f` that traps
with `c`. -/
theorem trapsExplicitX_trapEnv (env : Env) (c : TrapCode) (hp : p.funcs = [])
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) (hlf : LinkFree f) {args : List Val}
    {cs : State} (hcs : ClifEntry f args cs) (htr : TrapsExplicitC env p cs) {fuel : Nat}
    (hrun : runLoop env p fuel cs = .trapped c) : TrapsExplicitX (trapEnv env c) p cs := by
  have hx : cs.toX = ⟨cs, []⟩ := by simp [State.toX, hcs.callers]
  have hreach : ∀ xs, ReachX (trapEnv env c) p cs.toX xs →
      xs.tries = [] ∧ Reach env p cs xs.s ∧ LInv (p.only f) xs.s ∧ xs.s.callers = [] :=
    fun xs h => reachX_trapEnv env c hp hf hlf h cs hx (linv_entry hcs) hcs.callers
  have hnt : ∀ (B : Block), B ∈ cs.frame.func.blocks → B.term.isTry = false := by
    rw [hcs.func]; exact hf
  refine ⟨fun xs c'' st rest hr hs hb => ?_, fun xs c'' fn args et _ _ _ _ B hB e => ?_,
    fun xs c'' callee args et _ _ _ _ B hB e => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ _ g hg => by simp [hp] at hg,
    fun _ _ _ _ _ _ _ _ _ _ g hg => by simp [hp] at hg⟩
  · obtain ⟨-, hR, -, -⟩ := hreach xs hr
    have hse : step env p xs.s = .trapped c'' := by
      rcases step_trapRel env c hp xs.s with e | ⟨-, m, e⟩
      · rw [← e, hs]
      · rw [hs] at e; cases e
    obtain ⟨n, hn⟩ := reach_trapped_runLoop hR hse
    have hc : c'' = c := trapped_det hn hrun
    subst hc
    rcases htr.stmt xs.s c'' st rest hR hse hb with h | h
    · exact h
    · exact absurd hs (step_call_trap_stuck env c'' hp hb h hse)
  · have := hnt B hB; rw [e] at this; cases this
  · have := hnt B hB; rw [e] at this; cases this

/-- **The run with unwinding of `trapEnv env c`**: where `f`'s run traps with `c`, it traps
with `c` (an explicit trap) or ends with an exception (a callee trapped with `c`). -/
theorem runLoopX_trapEnv (env : Env) (c : TrapCode) (hp : p.funcs = [])
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) (hlf : LinkFree f) :
    ∀ (fuel : Nat) (s : State), LInv (p.only f) s → s.callers = [] →
      runLoop env p fuel s = .trapped c →
      runLoopX (trapEnv env c) p fuel ⟨s, []⟩ = .trapped c ∨
        ∃ e m, runLoopX (trapEnv env c) p fuel ⟨s, []⟩ = .unwound e m
  | 0, _, _, _, h => by simp at h
  | fuel + 1, s, hI, hcl, h => by
    have hnt := noTry_of_lframe hf hI.1
    have hnp := pendingOf_none hnt
    rw [runLoop_succ] at h
    unfold runLoopX
    cases hr : raiseAt? (trapEnv env c) p s with
    | some em =>
      obtain ⟨e, m⟩ := em
      obtain ⟨m', hm⟩ := stepX_raise hcl hnp hr
      rw [hm]
      exact .inr ⟨e, m', rfl⟩
    | none =>
      have hsx : stepX (trapEnv env c) p ⟨s, []⟩ =
          liftStep ⟨s, []⟩ (step (trapEnv env c).toEnv p s) := by
        unfold stepX; rw [hr]
      rw [hsx]
      rcases step_trapRel env c hp s with e | ⟨h1, m, h2⟩
      · rw [e]
        cases hst : step env p s with
        | next s' =>
          rw [hst] at h
          have hI' := (step_next_linv (linkFree_only hlf) hI hst
            (fun g hg => by simp [hp] at hg)).1
          have hcl' : s'.callers = [] :=
            step_bare_callers (linkFree_only hlf) hI.1 hcl (by rw [bare_self hp]; exact hst)
          rw [liftStep_next hcl hcl']
          exact runLoopX_trapEnv env c hp hf hlf fuel s' hI' hcl' h
        | done v m => rw [hst] at h; cases h
        | trapped c' => rw [hst] at h; cases h; exact .inl rfl
        | stuck m => rw [hst] at h; cases h
      · have := raiseAt_of_trapRel env c hp hnt h1 h2
        rw [hr] at this; cases this

/-- **The CLIF side of a callee trap**: for a run of `f` (without `try_call`s and
`return_call`s, in a program without functions) that traps with `c` under `TrapsExplicitC`, the
run with unwinding of `trapEnv env c` satisfies `TrapsExplicitX` and traps with `c` or ends with
an exception. -/
theorem trapEnv_of_trapped (env : Env) (c : TrapCode) (hp : p.funcs = [])
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) (hlf : LinkFree f) {args : List Val}
    {cs : State} (hcs : ClifEntry f args cs) (htr : TrapsExplicitC env p cs) {fuel : Nat}
    (hrun : runLoop env p fuel cs = .trapped c) :
    TrapsExplicitX (trapEnv env c) p cs ∧
      (runLoopX (trapEnv env c) p fuel cs.toX = .trapped c ∨
        ∃ e m, runLoopX (trapEnv env c) p fuel cs.toX = .unwound e m) := by
  have hx : cs.toX = ⟨cs, []⟩ := by simp [State.toX, hcs.callers]
  refine ⟨trapsExplicitX_trapEnv env c hp hf hlf hcs htr hrun, ?_⟩
  rw [hx]
  exact runLoopX_trapEnv env c hp hf hlf fuel cs (linv_entry hcs) hcs.callers hrun

end

end E2E
