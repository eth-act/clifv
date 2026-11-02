import FV.E2E.TrapCallClifRun

/-!
# Callee traps of `try_call`/`try_call_indirect`: the CLIF side (S9b, #375)

S9a (`FV/E2E/TrapCallClif*.lean`) turns a callee trap with code `c` into an exception of the run
with unwinding of `trapEnv env c`, for functions without `try_call` terminators: at a `try_call`
that exception would be caught by the handler. For a `try_call` whose callee traps the proof
stops at the call instead (`FV/E2E/TrapCallTryStop.lean`); here the CLIF facts it needs:

* `TrapsExplicitCT`: `TrapsExplicitC` without its `tryCall`/`tryCallInd` clauses (traps of the
  callees of `try_call`s allowed); `TrapsExplicitC.toT`.
* `tryPre_ne_trap`, `tryIndPre_ne_trap`: the preludes of a `try_call` never trap;
  `step_try_trap_stuck`: a `try_call` step that traps with `c` in `env` (its callee trapped) does
  not trap with `c` in `trapEnv env c`'s environment;
* `raiseAt_of_trapRel_try`: there, the step of the run with unwinding raises.
-/

namespace E2E

open Clif Backend.Proof Backend.Proof.Driver

/-! ## The premise -/

/-- **The run premise with callee traps, `try_call` callees included** (`TrapsExplicitC`
without its `tryCall`/`tryCallInd` clauses): a statement traps only if it is an explicitly
trapping instruction or a call whose callee trapped; a `try_call`/`try_call_indirect` traps
only inside its callee (its preludes never trap, `tryPre_ne_trap`). Still excluded:
memory-access traps. -/
structure TrapsExplicitCT (env : Env) (p : Program) (cs : State) : Prop where
  stmt : ∀ s c st rest, Reach env p cs s → step env p s = .trapped c →
    s.frame.body = st :: rest → explicitTrapInst st.inst = true ∨ CallInst st.inst
  indirect : ∀ s st rest sig callee args, Reach env p cs s → s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ cs.frame.func.blocks, st ∈ B.body) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat
  tryIndirect : ∀ s callee args et, Reach env p cs s → s.frame.body = [] →
    s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ cs.frame.func.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat

/-- `TrapsExplicitC` gives `TrapsExplicitCT` (the premise is weaker). -/
theorem TrapsExplicitC.toT {env : Env} {p : Program} {cs : State} (h : TrapsExplicitC env p cs) :
    TrapsExplicitCT env p cs :=
  ⟨h.stmt, h.indirect, h.tryIndirect⟩

section
variable {env : Env} {c : TrapCode} {p : Program}

/-! ## The preludes of a `try_call` never trap -/

theorem mapM_ne_trap {α β : Type} (F : α → Res β) (hF : ∀ a c', F a ≠ .trap c') :
    ∀ (l : List α) (c' : TrapCode), l.mapM F ≠ .trap c'
  | [], c' => by simp [List.mapM_nil, pure]
  | a :: l, c' => by
    rw [List.mapM_cons]
    cases h : F a with
    | ok b =>
      simp only [Res.ok_bind]
      cases h2 : l.mapM F with
      | ok bs => simp [pure]
      | trap c'' => exact absurd h2 (mapM_ne_trap F hF l c'')
      | stuck m => simp
    | trap c'' => exact absurd h (hF a c'')
    | stuck m => simp

theorem tryNormal_ne_trap (et : ExnTable) (base : ValueId) (c' : TrapCode) :
    tryNormal et base ≠ .trap c' := by
  unfold tryNormal
  have h := mapM_ne_trap (β := ValueId) (fun
    | .val v => pure v
    | .ret i => pure (base + i)
    | .exn _ => .stuck "try_call: exception payload on the normal-return edge")
    (fun a c'' => by cases a <;> simp [pure]) et.normal.args
  cases hm : et.normal.args.mapM (fun
    | .val v => pure v
    | .ret i => pure (base + i)
    | .exn _ => (.stuck "try_call: exception payload on the normal-return edge" : Res ValueId)) with
  | ok bs => simp [pure]
  | trap c'' => exact absurd hm (h c'')
  | stuck m => simp

theorem tryPre_ne_trap (fr : Frame) (fn : FnRef) (et : ExnTable) (c' : TrapCode) :
    tryPre fr fn et ≠ .trap c' := by
  unfold tryPre
  cases fr.func.extern? fn with
  | none => simp
  | some ext =>
    simp only [Res.ofOption_some, Res.ok_bind]
    cases fr.func.sigDecls.lookup et.sig with
    | none => simp
    | some sig =>
      simp only [Res.ofOption_some, Res.ok_bind, Res.check]
      split
      · simp only [Res.ok_bind]
        cases h : tryNormal et fr.func.freshValue with
        | ok bc => simp [pure]
        | trap c'' => exact absurd h (tryNormal_ne_trap et _ c'')
        | stuck m => simp
      · simp

theorem tryIndPre_ne_trap (fr : Frame) (et : ExnTable) (c' : TrapCode) :
    tryIndPre fr et ≠ .trap c' := by
  unfold tryIndPre
  cases fr.func.sigDecls.lookup et.sig with
  | none => simp
  | some sig =>
    simp only [Res.ofOption_some, Res.ok_bind]
    cases h : tryNormal et fr.func.freshValue with
    | ok bc => simp [pure]
    | trap c'' => exact absurd h (tryNormal_ne_trap et _ c'')
    | stuck m => simp

theorem getMany_regs {fr fr' : Frame} (h : fr.regs = fr'.regs) :
    ∀ xs : List ValueId, fr.getMany xs = fr'.getMany xs
  | [] => rfl
  | x :: xs => by simp only [Frame.getMany, Frame.get, h, getMany_regs h xs]

theorem callArgs_tryState (s : State) (bc : BlockCall) (fn : FnRef) (args : List ValueId) :
    Opt.callArgs (tryState s bc).frame fn args = Opt.callArgs s.frame fn args := by
  simp only [Opt.callArgs, tryState, getMany_regs (fr := { s.frame with body := [], term := .jump bc })
    (fr' := s.frame) rfl]

theorem indPre_tryState (s : State) (bc : BlockCall) (sig : Nat) (callee : ValueId)
    (args : List ValueId) :
    indPre (tryState s bc).frame sig callee args = indPre s.frame sig callee args := by
  simp only [indPre, tryState, getMany_regs (fr := { s.frame with body := [], term := .jump bc })
    (fr' := s.frame) rfl, Frame.get]

/-! ## A trapping `try_call` step -/

/-- **A `try_call`/`try_call_indirect` step that traps with `c` in `env` does not trap with `c`
in `trapEnv`'s environment** (its callee trapped; there it is `stuck`). -/
theorem step_try_trap_stuck (env : Env) (c : TrapCode) (hp : p.funcs = []) {s : State}
    (hb : s.frame.body = []) {et : ExnTable} (hT : IsTryWith s.frame.term et)
    (h : step env p s = .trapped c) : step (trapEnv env c).toEnv p s ≠ .trapped c := by
  intro h2
  rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
  · rw [step_try _ _ s hb ht] at h h2
    cases hpre : tryPre s.frame fn et with
    | ok r =>
      obtain ⟨n, b, bc⟩ := r
      rw [hpre] at h h2
      simp only [StepResult.ofRes] at h h2
      cases ha : Opt.callArgs (tryState s bc).frame fn args with
      | ok r =>
        obtain ⟨ext, vals⟩ := r
        rw [ha] at h h2
        simp only [StepResult.ofRes] at h h2
        obtain ⟨g, he, hg⟩ := callCont_trap_inv hp h
        simp only [Opt.callCont, func?_nil hp, trapEnv_toEnv_extern, he, Option.map, hg,
          trapOut_self, XOutcome.toOutcome] at h2
        cases h2
      | trap c' => exact callArgs_ne_trap _ fn args ha
      | stuck m => rw [ha] at h; cases h
    | trap c' => exact tryPre_ne_trap _ fn et c' hpre
    | stuck m => rw [hpre] at h; cases h
  · rw [step_tryInd _ _ s hb ht] at h h2
    cases hpre : tryIndPre s.frame et with
    | ok r =>
      obtain ⟨n, b, bc⟩ := r
      rw [hpre] at h h2
      simp only [StepResult.ofRes] at h h2
      cases ha : indPre (tryState s bc).frame et.sig callee args with
      | ok r =>
        obtain ⟨d, a, v⟩ := r
        rw [ha] at h h2
        simp only [StepResult.ofRes] at h h2
        have hx := indCont_trap_inv hp h
        obtain ⟨name, g, hf, he, hs, hty, hg⟩ := callExternAt_trap_inv hx
        simp only [indCont, find?_nil hp] at h2
        have hx2 : callExternAt (trapEnv env c).toEnv p (tryState s bc).mem d a v =
            .stuck "callee unwound (Clif.run has no unwinding)" := by
          unfold callExternAt
          have hn : (trapEnv env c).toEnv.names = env.names := rfl
          have hs' : (trapEnv env c).toEnv.sigOf = env.sigOf := rfl
          rw [hn, hs', hf]
          simp only [Res.ofOption_some, Res.ok_bind, trapEnv_toEnv_extern, he, Option.map, hs,
            Res.check_true, checkTys, hty, beq_self_eq_true, hg, trapOut_self, XOutcome.toOutcome]
        rw [hx2] at h2
        cases h2
      | trap c' => exact indPre_ne_trap _ et.sig callee args ha
      | stuck m => rw [ha] at h; cases h
    | trap c' => exact tryIndPre_ne_trap _ et c' hpre
    | stuck m => rw [hpre] at h; cases h

/-- **Where `env`'s `try_call`/`try_call_indirect` step traps with `c` and `trapEnv`'s is
`stuck`, the step of the run with unwinding raises** (the call's extern traps with `c`). -/
theorem raiseAt_of_trapRel_try (env : Env) (c : TrapCode) (hp : p.funcs = []) {s : State}
    (hb : s.frame.body = []) {et : ExnTable} (hT : IsTryWith s.frame.term et)
    (h1 : step env p s = .trapped c) :
    raiseAt? (trapEnv env c) p s = some (trapExn, s.mem) := by
  rcases hT with ⟨fn, args, ht⟩ | ⟨callee, args, ht⟩
  · rw [step_try _ _ s hb ht] at h1
    rcases ofRes_trapped_inv h1 with hpre | ⟨⟨n, b, bc⟩, hpre, hk⟩
    · exact absurd hpre (tryPre_ne_trap _ fn et c)
    rcases ofRes_trapped_inv hk with ha | ⟨⟨ext, vals⟩, ha, hk⟩
    · exact absurd ha (callArgs_ne_trap _ fn args)
    obtain ⟨g, he, hg⟩ := callCont_trap_inv hp hk
    have hpre' : (do
        let ext ← Res.ofOption s!"unknown function reference fn{fn}" (s.frame.func.extern? fn)
        let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (s.frame.func.sigDecls.lookup et.sig)
        Res.check (AbiParam.tys sig.params == AbiParam.tys ext.sig.params &&
            AbiParam.tys sig.returns == AbiParam.tys ext.sig.returns)
          s!"try_call: sig{et.sig} is not the signature of fn{fn}"
        let base := s.frame.func.freshValue
        let bc ← tryNormal et base
        pure (ext.sig.returns.length, base, bc) : Res (Nat × ValueId × BlockCall)) =
        .ok (n, b, bc) := hpre
    simp only [raiseAt?, hb, ht, tryCallRaise, hpre']
    rw [callArgs_tryState] at ha
    exact callRaise_of_trap hp ha he hg
  · rw [step_tryInd _ _ s hb ht] at h1
    rcases ofRes_trapped_inv h1 with hpre | ⟨⟨n, b, bc⟩, hpre, hk⟩
    · exact absurd hpre (tryIndPre_ne_trap _ et c)
    rcases ofRes_trapped_inv hk with ha | ⟨⟨d, a, v⟩, ha, hk⟩
    · exact absurd ha (indPre_ne_trap _ et.sig callee args)
    have hx := indCont_trap_inv hp hk
    have hpre' : (do
        let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (s.frame.func.sigDecls.lookup et.sig)
        let base := s.frame.func.freshValue
        let bc ← tryNormal et base
        pure (sig.returns.length, base, bc) : Res (Nat × ValueId × BlockCall)) =
        .ok (n, b, bc) := hpre
    simp only [raiseAt?, hb, ht, tryCallIndRaise, hpre']
    rw [indPre_tryState] at ha
    exact callIndRaise_of_trap hp ha hx

end

end E2E
