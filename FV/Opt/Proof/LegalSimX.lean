import FV.Opt.Proof.LegalSimS
import FV.Opt.LegalExn

/-!
# The refinement theorem of `Opt.Legal.check` with unwinding (S10e, #232)

`check_refinesX`: for a legalisation `g` of `f` accepted by `Opt.Legal.check` and by the
handler-edge check `Opt.Legal.exnOk`, the run of `g` with unwinding (`Clif.runLoopX`) refines
the run of `f` with unwinding: a return is a return of the expanded results with the same
memory, a trap the same trap, and an exception leaving `f` (`unwound e m`) the same exception
leaving `g` with the same memory.

* Steps where no callee unwinds are `Clif.step`'s (`Clif.stepX_of_not_stuck`), simulated by
  `FV/Opt/Proof/LegalSimS.lean` (`step_sim`'s stepwise copy), whose target steps are steps
  with unwinding too (`TStep.runLoopX`: a target step that continues raises nothing).
* A `call` whose extern unwinds (`sim_call_raise`): the target's call has the expanded
  arguments, so it unwinds with the same exception and memory (`ExtLegalX`); both frames are
  left (`Clif.unwindFrom`, the same slots).
* A `call_indirect` whose extern unwinds (`sim_callInd_raise`): the same statement on the same
  values, resolving to the same extern.
* A `try_call` whose callee unwinds (`sim_try_raise`): the target unwinds with the same
  exception; the exception tables are related item by item (`exnOk`, at the target's
  terminator: `InCode`, the target runs in `g`'s code), so either neither table catches it and
  both frames are left, or both continue at related handlers with the payload bound at fresh
  values, and after the jumps to the handler blocks the frames are related again.
* `sim_runX`: the fuel induction.

Premises beyond `check_refines`'s: `ExtLegalX` and `EnvKeepsAllocsX` (the environment's
contracts for its unwinding externs), and the source run's `NoMemTrapX`/`NoIndInternalX` over
the states the run with unwinding reaches.
-/

namespace Opt.Legal.X

open Clif Opt Opt.Legalize128 Opt.Legal

/-! ## The environment's contracts for unwinding externs -/

/-- An extern called with the arguments expanded by the ABI groups of its declared signature
unwinds where the original call unwinds, with the same exception and memory. -/
def ExtLegalX (env : XEnv) : Prop :=
  ∀ name h, env.extern name = some h → ∀ (sig : Signature) gs, groups sig.params = some gs →
    ∀ vals vals' m, vals.map (·.ty) = AbiParam.tys sig.params → ExpRel gs vals vals' →
    ∀ e m', h vals m = .unwound e m' → h vals' m = .unwound e m'

/-- An extern that unwinds leaves the caller's allocations. -/
def EnvKeepsAllocsX (env : XEnv) : Prop :=
  ∀ name h, env.extern name = some h → ∀ vals m e m', h vals m = .unwound e m' →
    m'.allocs = m.allocs

/-- An exception an extern raises carries the two payload words a handler may read (`exn0`,
`exn1`; Rust's personality installs the exception object and a selector). -/
def ExnArityOk (env : XEnv) : Prop :=
  ∀ name h, env.extern name = some h → ∀ vals m e m', h vals m = .unwound e m' →
    2 ≤ e.payload.length

/-- The environment's side of the refinement with unwinding. -/
structure EnvOkX (env : XEnv) (C : Ctx) (p p' : Program) : Prop where
  base : EnvOk env.toEnv C p p'
  extX : ExtLegalX env
  keepX : EnvKeepsAllocsX env
  arity : ExnArityOk env

/-! ## Reachability with unwinding -/

/-- Reachability by continuing steps with unwinding. -/
inductive SReachX (env : XEnv) (p : Program) : XState → XState → Prop
  | refl (xs : XState) : SReachX env p xs xs
  | step {xs xs' xs'' : XState} : stepX env p xs = .next xs' → SReachX env p xs' xs'' →
      SReachX env p xs xs''

/-- No state the run with unwinding reaches from `s` traps at a load or store. -/
def NoMemTrapX (env : XEnv) (p : Program) (s : State) : Prop :=
  ∀ xs', SReachX env p ⟨s, []⟩ xs' → MemTrapFree env.toEnv p xs'.s

/-- No state the run with unwinding reaches from `s` calls a function of `p` indirectly. -/
def NoIndInternalX (env : XEnv) (p : Program) (f : Function) (s : State) : Prop :=
  ∀ xs', SReachX env p ⟨s, []⟩ xs' → IndExt env.toEnv p f xs'.s

theorem NoMemTrapX.next {env : XEnv} {p : Program} {s s1 : State} (h : NoMemTrapX env p s)
    (hs : stepX env p ⟨s, []⟩ = .next ⟨s1, []⟩) : NoMemTrapX env p s1 :=
  fun xs' hr => h xs' (.step hs hr)

theorem NoIndInternalX.next {env : XEnv} {p : Program} {f : Function} {s s1 : State}
    (h : NoIndInternalX env p f s) (hs : stepX env p ⟨s, []⟩ = .next ⟨s1, []⟩) :
    NoIndInternalX env p f s1 :=
  fun xs' hr => h xs' (.step hs hr)

/-! ## Target steps are steps with unwinding -/

/-- A step of `Clif.run`'s semantics that continues between states without callers is a step
with unwinding. -/
theorem stepX_of_next {env : XEnv} {p : Program} {s s' : State}
    (h : step env.toEnv p s = .next s') (hc : s.callers = []) (hc' : s'.callers = []) :
    stepX env p ⟨s, []⟩ = .next ⟨s', []⟩ := by
  rw [stepX_of_not_stuck (xs := ⟨s, []⟩) (fun msg hm => by
    have : step env.toEnv p s = .stuck msg := hm
    rw [h] at this; cases this), show (⟨s, []⟩ : XState).s = s from rfl, h]
  simp [liftStep, hc, hc']

theorem runLoopX_next {env : XEnv} {p : Program} {xs xs' : XState} (h : stepX env p xs = .next xs')
    (n : Nat) : runLoopX env p (n + 1) xs = runLoopX env p n xs' := by
  rw [Clif.runLoopX, h]

theorem tstep_runLoopX {env : XEnv} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    (h : S.TStep env.toEnv p' fr' m fr1' m1) :
    ∃ k, ∀ n, runLoopX env p' (n + k) ⟨⟨fr', [], m⟩, []⟩ =
      runLoopX env p' n ⟨⟨fr1', [], m1⟩, []⟩ := by
  induction h with
  | refl => exact ⟨0, fun _ => rfl⟩
  | step hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n => ?_⟩
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    rw [runLoopX_next (stepX_of_next hs rfl rfl)]
    exact hk n

/-! ## The target runs in `g`'s code -/

/-- The frame runs in `g`'s code: at the terminator of a block of `g`, or at a pending jump
(after a `try_call`'s call). -/
def InCode (g : Function) (fr : Frame) : Prop :=
  fr.func = g ∧ ((∃ B ∈ g.blocks, fr.term = B.term) ∨ (fr.body = [] ∧ ∃ bc, fr.term = .jump bc))

theorem continueWith_next {s s' : State} {rest : List Stmt} {rs : List ValueId} {vs : List Val}
    {m : Mem} (h : continueWith s rest rs vs m = .next s') :
    s'.callers = s.callers ∧ s'.frame.func = s.frame.func ∧ s'.frame.term = s.frame.term ∧
      s'.frame.body = rest := by
  unfold continueWith at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

theorem stepCall_next {env : Env} {p : Program} {s s' : State} {rest : List Stmt}
    {rs : List ValueId} {fn : FnRef} {args : List ValueId}
    (h : stepCall env p s rest rs fn args = .next s') (hc : s'.callers = s.callers) :
    s'.frame.func = s.frame.func ∧ s'.frame.term = s.frame.term ∧ s'.frame.body = rest := by
  unfold stepCall at h
  simp only at h
  generalize (do
    let ext ← Res.ofOption s!"unknown function reference fn{fn}" (s.frame.func.extern? fn)
    let vals ← s.frame.getMany args
    checkTys s!"arguments of call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
    pure (ext, vals) : Res (ExtFunc × List Val)) = r at h
  cases r with
  | trap c => cases h
  | stuck msg => cases h
  | ok ev =>
    obtain ⟨ext, vals⟩ := ev
    simp only [StepResult.ofRes_ok] at h
    split at h
    · split at h
      · cases he : enterFunc _ vals s.mem with
        | ok q =>
          rw [he] at h
          simp only [StepResult.ofRes_ok, StepResult.next.injEq] at h
          subst h
          simp at hc
        | trap c => rw [he] at h; cases h
        | stuck msg => rw [he] at h; cases h
      · cases h
    · split at h
      · split at h
        · split at h
          · exact (continueWith_next h).2
          · cases h
        · cases h
        · cases h
        · cases h
      · cases h

theorem stepCallIndirect_next {env : Env} {p : Program} {s s' : State} {rest : List Stmt}
    {rs : List ValueId} {sig : Nat} {callee : ValueId} {args : List ValueId}
    (h : stepCallIndirect env p s rest rs sig callee args = .next s') (hc : s'.callers = s.callers) :
    s'.frame.func = s.frame.func ∧ s'.frame.term = s.frame.term ∧ s'.frame.body = rest := by
  unfold stepCallIndirect at h
  simp only at h
  generalize (do
    let declared ← Res.ofOption s!"unknown signature sig{sig}" (s.frame.func.sigDecls.lookup sig)
    let cv ← s.frame.get callee
    let cv64 ← Res.ofOption "call_indirect: callee is not i64" (cv.as? .i64)
    let vals ← s.frame.getMany args
    pure (declared, cv64.toNat, vals) : Res (Signature × Nat × List Val)) = r at h
  cases r with
  | trap c => cases h
  | stuck msg => cases h
  | ok q =>
    obtain ⟨declared, addr, vals⟩ := q
    simp only [StepResult.ofRes_ok] at h
    split at h
    · split at h
      · cases he : enterFunc _ vals s.mem with
        | ok q =>
          rw [he] at h
          simp only [StepResult.ofRes_ok, StepResult.next.injEq] at h
          subst h
          simp at hc
        | trap c => rw [he] at h; cases h
        | stuck msg => rw [he] at h; cases h
      · cases h
    · cases hx : callExternAt env p s.mem declared addr vals with
      | ok q =>
        rw [hx] at h
        simp only [StepResult.ofRes_ok] at h
        exact (continueWith_next h).2
      | trap c => rw [hx] at h; cases h
      | stuck msg => rw [hx] at h; cases h

theorem block?_mem {f : Function} {id : BlockId} {B : Block} (h : f.block? id = some B) :
    B ∈ f.blocks := by
  unfold Function.block? at h
  exact List.mem_of_find?_eq_some h

theorem enterBlock_next {fr fr1 : Frame} {bc : BlockCall} (h : enterBlock fr bc = .ok fr1) :
    fr1.func = fr.func ∧ ∃ B ∈ fr.func.blocks, fr1.term = B.term := by
  obtain ⟨B, args, regs, hB, -, -, -, rfl⟩ := enterBlock_ok h
  exact ⟨rfl, B, block?_mem hB, rfl⟩

theorem ofRes_enter_next {fr : Frame} {bc : BlockCall} {cs : List (Frame × List ValueId)}
    {mm : Mem} {s' : State}
    (h : StepResult.ofRes (enterBlock fr bc) (fun fr1 => .next ⟨fr1, cs, mm⟩) = .next s') :
    s'.frame.func = fr.func ∧ ∃ B ∈ fr.func.blocks, s'.frame.term = B.term := by
  cases he : enterBlock fr bc with
  | ok fr1 =>
    rw [he] at h
    simp only [StepResult.ofRes_ok, StepResult.next.injEq] at h
    subst h
    exact enterBlock_next he
  | trap c => rw [he] at h; cases h
  | stuck msg => rw [he] at h; cases h

theorem stepTryCall_next {env : Env} {p : Program} {s s' : State} {fn : FnRef}
    {args : List ValueId} {et : ExnTable} (h : stepTryCall env p s fn args et = .next s')
    (hc : s'.callers = s.callers) :
    s'.frame.func = s.frame.func ∧ s'.frame.body = [] ∧ ∃ bc, s'.frame.term = .jump bc := by
  unfold stepTryCall StepResult.ofRes at h
  dsimp only at h
  split at h
  · rename_i q _
    obtain ⟨h1, h2, h3⟩ := stepCall_next h hc
    exact ⟨h1, h3, _, h2⟩
  · cases h
  · cases h

theorem stepTryCallIndirect_next {env : Env} {p : Program} {s s' : State} {callee : ValueId}
    {args : List ValueId} {et : ExnTable} (h : stepTryCallIndirect env p s callee args et = .next s')
    (hc : s'.callers = s.callers) :
    s'.frame.func = s.frame.func ∧ s'.frame.body = [] ∧ ∃ bc, s'.frame.term = .jump bc := by
  unfold stepTryCallIndirect StepResult.ofRes at h
  dsimp only at h
  split at h
  · rename_i q _
    obtain ⟨h1, h2, h3⟩ := stepCallIndirect_next h hc
    exact ⟨h1, h3, _, h2⟩
  · cases h
  · cases h

/-- **The shape of a step that continues without callers**: the same function; the same
terminator (a statement), a block's terminator (a branch) or a pending jump (a `try_call`'s
call). -/
theorem step_next_shape {env : Env} {p : Program} {fr fr1 : Frame} {m m1 : Mem}
    (h : step env p ⟨fr, [], m⟩ = .next ⟨fr1, [], m1⟩)
    (hrc : fr.body = [] → ∀ fn args, fr.term ≠ .returnCall fn args) :
    fr1.func = fr.func ∧ ((fr.body ≠ [] ∧ fr1.term = fr.term) ∨
      (∃ B ∈ fr.func.blocks, fr1.term = B.term) ∨ (fr1.body = [] ∧ ∃ bc, fr1.term = .jump bc)) := by
  cases hb : fr.body with
  | nil =>
    rw [step_term env p _ hb] at h
    simp only at h
    cases ht : fr.term with
    | jump dest =>
      rw [ht] at h
      obtain ⟨h1, h2⟩ := ofRes_enter_next h
      exact ⟨h1, .inr (.inl h2)⟩
    | brif c t e =>
      rw [ht] at h
      simp only [stepTerm] at h
      cases hc : fr.get c with
      | ok cv =>
        rw [hc] at h
        simp only [StepResult.ofRes_ok] at h
        obtain ⟨h1, h2⟩ := ofRes_enter_next h
        exact ⟨h1, .inr (.inl h2)⟩
      | trap c => rw [hc] at h; cases h
      | stuck msg => rw [hc] at h; cases h
    | brTable x d tbl =>
      rw [ht] at h
      simp only [stepTerm] at h
      cases hc : fr.get x with
      | ok cv =>
        rw [hc] at h
        simp only [StepResult.ofRes_ok] at h
        obtain ⟨h1, h2⟩ := ofRes_enter_next h
        exact ⟨h1, .inr (.inl h2)⟩
      | trap c => rw [hc] at h; cases h
      | stuck msg => rw [hc] at h; cases h
    | ret xs =>
      rw [ht] at h
      simp only [stepTerm] at h
      cases hc : fr.getMany xs with
      | ok vals =>
        rw [hc] at h
        simp only [StepResult.ofRes_ok, returnValues] at h
        cases hk : checkTys (toString "return values of %" ++ toString fr.func.name) vals
          (AbiParam.tys fr.func.sig.returns) with
        | ok u => rw [hk] at h; simp at h
        | trap c => rw [hk] at h; cases h
        | stuck msg => rw [hk] at h; cases h
      | trap c => rw [hc] at h; cases h
      | stuck msg => rw [hc] at h; cases h
    | returnCall fn args => exact absurd ht (hrc hb fn args)
    | trap c => rw [ht] at h; cases h
    | tryCall fn args et =>
      rw [ht] at h
      obtain ⟨h1, h2, h3⟩ := stepTryCall_next h rfl
      exact ⟨h1, .inr (.inr ⟨h2, h3⟩)⟩
    | tryCallIndirect callee args et =>
      rw [ht] at h
      obtain ⟨h1, h2, h3⟩ := stepTryCallIndirect_next h rfl
      exact ⟨h1, .inr (.inr ⟨h2, h3⟩)⟩
  | cons st rest =>
    have hne : st :: rest ≠ [] := List.cons_ne_nil _ _
    unfold step at h
    simp only [hb] at h
    split at h
    · obtain ⟨h1, h2, -⟩ := stepCall_next h rfl
      exact ⟨h1, .inl ⟨hne, h2⟩⟩
    · obtain ⟨h1, h2, -⟩ := stepCallIndirect_next h rfl
      exact ⟨h1, .inl ⟨hne, h2⟩⟩
    · cases he : evalInst fr m _ with
      | ok q =>
        rw [he] at h
        simp only [StepResult.ofRes_ok] at h
        obtain ⟨-, h1, h2, -⟩ := continueWith_next h
        exact ⟨h1, .inl ⟨hne, h2⟩⟩
      | trap c => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h

theorem InCode.step {g : Function} (hnr : ∀ B ∈ g.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    {env : Env} {p : Program} {fr fr1 : Frame} {m m1 : Mem} (hc : InCode g fr)
    (h : step env p ⟨fr, [], m⟩ = .next ⟨fr1, [], m1⟩) : InCode g fr1 := by
  obtain ⟨hf, hpos⟩ := hc
  obtain ⟨h1, h2⟩ := step_next_shape h (fun _ fn args he => by
    rcases hpos with ⟨B, hB, ht⟩ | ⟨-, bc, ht⟩
    · exact hnr B hB fn args (ht ▸ he)
    · rw [ht] at he; cases he)
  refine ⟨h1.trans hf, ?_⟩
  rcases h2 with ⟨hne, h2⟩ | h2 | h2
  · rw [h2]
    rcases hpos with hpos | ⟨hb, -⟩
    · exact .inl hpos
    · exact absurd hb hne
  · rw [hf] at h2; exact .inl h2
  · exact .inr h2

theorem tstep_inCode {g : Function} (hnr : ∀ B ∈ g.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    {env : Env} {p : Program} {fr fr1 : Frame} {m m1 : Mem}
    (h : S.TStep env p fr m fr1 m1) (hc : InCode g fr) : InCode g fr1 := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (hc.step hnr hs)

/-! ## A call whose extern unwinds -/

theorem callRaise_inv {env : XEnv} {p : Program} {m : Mem} {fr : Frame} {fn : FnRef}
    {args : List ValueId} {x : Exn} {m1 : Mem} (h : callRaise env p m fr fn args = some (x, m1)) :
    ∃ ext vals g, fr.func.extern? fn = some ext ∧ fr.getMany args = .ok vals ∧
      vals.map (·.ty) = AbiParam.tys ext.sig.params ∧ p.func? ext.name = none ∧
      env.extern ext.name = some g ∧ g vals m = .unwound x m1 := by
  unfold callRaise at h
  split at h
  · rename_i ext vals hres
    cases hx : fr.func.extern? fn with
    | none => simp [hx, Res.ofOption, bind, Res.bind] at hres
    | some ext0 =>
    cases hv : fr.getMany args with
    | trap c => simp [hx, hv, Res.ofOption, bind, Res.bind] at hres
    | stuck msg => simp [hx, hv, Res.ofOption, bind, Res.bind] at hres
    | ok vals0 =>
    by_cases ht : vals0.map (·.ty) = AbiParam.tys ext0.sig.params
    · simp [hx, hv, Res.ofOption, bind, Res.bind, checkTys, Res.check, ht, pure] at hres
      obtain ⟨rfl, rfl⟩ := hres
      split at h
      · cases h
      · rename_i hp
        split at h
        · rename_i g hg
          split at h
          · rename_i e' m' hgo
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, _, g, rfl, rfl, ht, hp, hg, hgo⟩
          · cases h
        · cases h
    · simp [hx, hv, Res.ofOption, bind, Res.bind, checkTys, Res.check, ht] at hres
  · cases h

theorem callRaise_of {env : XEnv} {p : Program} {m : Mem} {fr : Frame} {fn : FnRef}
    {args : List ValueId} {ext : ExtFunc} {vals : List Val} {g : List Val → Mem → XOutcome}
    {x : Exn} {m1 : Mem} (hx : fr.func.extern? fn = some ext) (hv : fr.getMany args = .ok vals)
    (ht : vals.map (·.ty) = AbiParam.tys ext.sig.params) (hp : p.func? ext.name = none)
    (hg : env.extern ext.name = some g) (hgo : g vals m = .unwound x m1) :
    callRaise env p m fr fn args = some (x, m1) := by
  simp [callRaise, hx, hv, Res.ofOption, bind, Res.bind, checkTys, Res.check, ht, pure, hp, hg, hgo]

/-- A statement that is a `call` has the call plan. -/
theorem planOf_of_call {C : Ctx} {st : Stmt} {pl : Plan} (hp : planOf C st = some pl)
    {fn : FnRef} {args : List ValueId} (hi : st.inst = .call fn args) :
    ∃ e args' rg rs, pl = .call fn e args' rg rs := by
  cases pl with
  | same => exact absurd hi ((planOf_same hp).2.1 fn args)
  | pure pat ins outs => exact absurd hi ((planOf_pure_inst hp).1 fn args)
  | load rl rh q fl off => rw [(planOf_load hp).1] at hi; cases hi
  | store xl xh q fl off =>
    obtain ⟨⟨x, hx, -⟩, -⟩ := planOf_store hp
    rw [hx] at hi; cases hi
  | div op xl xh yl yh rl rh =>
    obtain ⟨x, y, r, hx, -⟩ := planOf_div hp
    rw [hx] at hi; cases hi
  | call fn' e args' rg rs =>
    obtain ⟨args0, gs, hx, -⟩ := planOf_call hp
    rw [hx] at hi
    cases hi
    exact ⟨e, args', rg, rs, rfl⟩
  | trap lo hi' nz code =>
    obtain ⟨c, hc, -⟩ := planOf_trap hp
    rcases hc with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] at hi <;> cases hi
  | callInd =>
    obtain ⟨sig, callee, args0, d, hx, -⟩ := planOf_callInd hp
    rw [hx] at hi; cases hi
  | callInd128 sig d callee args' rg rs =>
    obtain ⟨args0, gs, hx, -⟩ := planOf_callInd128 hp
    rw [hx] at hi; cases hi

/-- The memory after an exception leaves the frame `fr` (its slots freed). -/
def leftMem (fr : Frame) (m : Mem) : Mem := (m.free (fr.slots.map (·.2))).leave

/-- **A call whose extern unwinds**: the target's call of the expanded arguments unwinds with
the same exception and memory, and both frames are left. -/
theorem sim_call_raise {C : Ctx} (hG : Good C) {env : XEnv} {p p' : Program}
    (hE : EnvOkX env C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {fn : FnRef} {args : List ValueId}
    (hi : st.inst = .call fn args) {x : Exn} {m1 : Mem}
    (hr : callRaise env p m fr fn args = some (x, m1)) :
    stepX env p ⟨⟨fr, [], m⟩, []⟩ = .unwound x (leftMem fr m1) ∧
      stepX env p' ⟨⟨fr', [], m⟩, []⟩ = .unwound x (leftMem fr m1) := by
  constructor
  · simp [stepX, raiseAt?, hb, hi, hr, raiseIn, pendingOf, unwindFrom, leftMem]
  obtain ⟨ext, vals, g, hx, hv, ht, hp, hg, hgo⟩ := callRaise_inv hr
  have hcode0 := hR.code
  rw [hb] at hcode0
  obtain ⟨pl, hpl, hseg, -⟩ := code_cons hcode0
  obtain ⟨e, args', rg, rs, rfl⟩ := planOf_of_call hpl hi
  obtain ⟨args0, gs, hi0, -, hfe, hgs, -, hexp⟩ := planOf_call hpl
  rw [hi] at hi0
  obtain ⟨-, rfl⟩ : fn = fn ∧ args = args0 := by cases hi0; exact ⟨rfl, rfl⟩
  obtain ⟨rs', hs, -, -, s', hs', hfn⟩ := segOk_call hseg
  have hbody := take_drop_eq (l := fr'.body) (n := 1) rfl
  simp only [Plan.len] at hs
  rw [hs] at hbody
  rw [hR.func] at hx
  rw [hfe] at hx
  cases hx
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hlt : ∀ y ∈ args, y < C.T0 := fun y hy => ops_lt hG hB hst (by rw [hi]; exact hy)
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp hlt (getMany_holds hv)
  obtain ⟨gs0, rg0, hgs0, -, hpar', -⟩ := sigExp_spec hs'
  rw [hgs] at hgs0; cases hgs0
  have ht' : vals'.map (·.ty) = AbiParam.tys s'.params := by
    rw [hpar', AbiParam.tys, ← expRel_tys (groups_spec hgs) hexp' ht]
  have hfe' : fr'.func.extern? fn = some { ext with sig := s' } := by rw [hR.func']; exact hfn
  have hr' : callRaise env p' m fr' fn args' = some (x, m1) :=
    callRaise_of hfe' (holds_getMany hv') ht' (hE.base.tgt fn _ hfn) hg
      (hE.extX ext.name g hg ext.sig gs hgs vals vals' m ht hexp' x m1 hgo)
  simp only [List.singleton_append] at hbody
  obtain ⟨ts2, hb'⟩ : ∃ ts2, fr'.body = { results := rs', inst := .call fn args' } :: ts2 :=
    ⟨_, hbody⟩
  simp [stepX, raiseAt?, hb', hr', raiseIn, pendingOf, unwindFrom, leftMem, hR.slots]

/-! ## An indirect call whose extern unwinds -/

theorem externAtRaise_prefix {env : XEnv} {p p' : Program} (hpre : p.externNames <+: p'.externNames)
    {mem : Mem} {d : Signature} {a : Nat} {vals : List Val} {r : Exn × Mem}
    (h : externAtRaise env p mem d a vals = some r) : externAtRaise env p' mem d a vals = some r := by
  unfold externAtRaise at h ⊢
  cases hn : (env.names ++ p.externNames).find? fun n => mem.symbols n == some a with
  | none => rw [hn] at h; cases h
  | some n =>
    obtain ⟨t, ht⟩ := hpre
    have hn' : ((env.names ++ p'.externNames).find? fun n => mem.symbols n == some a) = some n := by
      rw [← ht, ← List.append_assoc, List.find?_append, hn, Option.some_or]
    rw [hn] at h
    rw [hn']
    exact h

theorem find?_names {l l' : List Function} (h : l'.map (·.name) = l.map (·.name))
    (q : String → Bool) (hl : l.find? (fun f => q f.name) = none) :
    l'.find? (fun f => q f.name) = none := by
  rw [List.find?_eq_none] at hl ⊢
  intro g hg
  have : g.name ∈ l.map (·.name) := by rw [← h]; exact List.mem_map_of_mem hg
  obtain ⟨g0, hg0, he⟩ := List.mem_map.mp this
  have := hl g0 hg0
  rw [he] at this
  exact this

theorem callIndRaise_inv {env : XEnv} {p : Program} {m : Mem} {fr : Frame} {sig : Nat}
    {callee : ValueId} {args : List ValueId} {r : Exn × Mem}
    (h : callIndRaise env p m fr sig callee args = some r) :
    ∃ declared cv cv64 vals, fr.func.sigDecls.lookup sig = some declared ∧ fr.get callee = .ok cv ∧
      cv.as? .i64 = some cv64 ∧ fr.getMany args = .ok vals ∧
      p.funcs.find? (fun f => m.symbols f.name == some cv64.toNat) = none ∧
      externAtRaise env p m declared cv64.toNat vals = some r := by
  unfold callIndRaise at h
  split at h
  · rename_i declared addr vals hres
    cases hd : fr.func.sigDecls.lookup sig with
    | none => simp [hd, Res.ofOption, bind, Res.bind] at hres
    | some d0 =>
    cases hc : fr.get callee with
    | trap c => simp [hd, hc, Res.ofOption, bind, Res.bind] at hres
    | stuck msg => simp [hd, hc, Res.ofOption, bind, Res.bind] at hres
    | ok cv =>
    cases h64 : cv.as? .i64 with
    | none => simp [hd, hc, h64, Res.ofOption, bind, Res.bind] at hres
    | some b =>
    cases hv : fr.getMany args with
    | trap c => simp [hd, hc, h64, hv, Res.ofOption, bind, Res.bind] at hres
    | stuck msg => simp [hd, hc, h64, hv, Res.ofOption, bind, Res.bind] at hres
    | ok vals0 =>
    simp [hd, hc, h64, hv, Res.ofOption, bind, Res.bind, pure] at hres
    obtain ⟨rfl, rfl, rfl⟩ := hres
    split at h
    · cases h
    · rename_i hf
      exact ⟨_, _, _, _, rfl, rfl, h64, rfl, hf, h⟩
  · cases h

/-- **An indirect call whose extern unwinds** (on the domain of `check`, `indOldB`): the target
runs the same statement on the same values, which resolves to the same extern. -/
theorem sim_callInd_raise {C : Ctx} (hG : Good C) (hold : indOldB C.f = true) {env : XEnv}
    {p p' : Program}
    (hE : EnvOkX env C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {sig : Nat} {callee : ValueId}
    {args : List ValueId} (hi : st.inst = .callIndirect sig callee args) {x : Exn} {m1 : Mem}
    (hr : callIndRaise env p m fr sig callee args = some (x, m1)) :
    stepX env p ⟨⟨fr, [], m⟩, []⟩ = .unwound x (leftMem fr m1) ∧
      stepX env p' ⟨⟨fr', [], m⟩, []⟩ = .unwound x (leftMem fr m1) := by
  constructor
  · simp [stepX, raiseAt?, hb, hi, hr, raiseIn, pendingOf, unwindFrom, leftMem]
  have hcode0 := hR.code
  rw [hb] at hcode0
  obtain ⟨pl, hpl, hseg, -⟩ := code_cons hcode0
  rcases planOf_callIndirect_eq hpl hi with rfl | ⟨d, args', rg, rs, rfl⟩
  rotate_left
  · exact (S.frel_not_callInd128 hR hold hb hpl).elim
  obtain ⟨hs, hdecl⟩ := segOk_callInd hseg
  have hbody := take_drop_eq (l := fr'.body) (n := 1) rfl
  simp only [Plan.len] at hs
  rw [hs, List.singleton_append] at hbody
  obtain ⟨ts2, hb'⟩ : ∃ ts2, fr'.body = st :: ts2 := ⟨_, hbody⟩
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  obtain ⟨sig0, callee0, args0, d0, hi0, -, -, hplain⟩ := planOf_callInd hpl
  rw [hi] at hi0
  cases hi0
  have hreg : ∀ y ∈ callee :: args, fr'.regs y = fr.regs y := fun y hy => by
    have hlt : y < C.T0 := ops_lt hG hB hst (by rw [hi]; simpa [instOps] using hy)
    have hpl' := hplain y (List.mem_append_left _ hy)
    exact hR.peq y hlt (by simpa [Ctx.plain] using hpl')
  obtain ⟨declared, cv, cv64, vals, hd, hc, h64, hv, hf, hx⟩ := callIndRaise_inv hr
  obtain ⟨hnames, hpre⟩ := hE.base.ind ⟨sig, .inl ⟨B, hB, st, hst, callee, args, hi⟩⟩
  have hd' : fr'.func.sigDecls.lookup sig = some declared := by
    rw [hR.func', hdecl sig callee args hi, ← hR.func]; exact hd
  have hc' : fr'.get callee = .ok cv := by
    simp only [Frame.get, hreg callee (List.mem_cons_self ..)]; exact hc
  have hv' : fr'.getMany args = .ok vals :=
    (getMany_congr fun y hy => hreg y (List.mem_cons_of_mem _ hy)).trans hv
  have hf' := find?_names hnames (fun n => m.symbols n == some cv64.toNat) hf
  have hr' : callIndRaise env p' m fr' sig callee args = some (x, m1) := by
    simp only [callIndRaise, hd', hc', h64, hv', Res.ofOption, bind, Res.bind, pure]
    simp only [hf']
    exact externAtRaise_prefix hpre hx
  simp [stepX, raiseAt?, hb', hi, hr', raiseIn, pendingOf, unwindFrom, leftMem, hR.slots]

/-! ## Handler edges -/

/-- The value id `Clif.tryHandler` passes for a handler argument (`base`: the first of the
fresh values the payload is bound to). -/
def exnId (base : ValueId) : TryArg → ValueId
  | .val v => v
  | .exn i => base + i
  | .ret _ => 0

theorem tryHandler_cases (base : ValueId) (blk : BlockId) :
    ∀ l : List TryArg,
    ((∀ i, TryArg.ret i ∉ l) ∧ tryHandler ⟨blk, l⟩ base =
      .ok { block := blk, args := l.map (exnId base) }) ∨
    ((∃ i, TryArg.ret i ∈ l) ∧ ∃ msg, tryHandler ⟨blk, l⟩ base = .stuck msg)
  | [] => .inl ⟨fun _ h => (by cases h), rfl⟩
  | a :: l => by
    have ih := tryHandler_cases base blk l
    unfold tryHandler at ih ⊢
    simp only [List.mapM_cons] at ih ⊢
    generalize hm : (List.mapM (m := Res) (α := TryArg) (β := ValueId) _ l) = r at ih ⊢
    cases r with
    | ok xs =>
      rcases ih with ⟨hn, h⟩ | ⟨hx, msg, h⟩
      · simp only [Res.ok_bind, Res.pure_eq, Res.ok.injEq, BlockCall.mk.injEq, true_and] at h
        subst h
        cases a with
        | val v => exact .inl ⟨fun i hi => by simp at hi; exact hn i hi, rfl⟩
        | exn j => exact .inl ⟨fun i hi => by simp at hi; exact hn i hi, rfl⟩
        | ret j => exact .inr ⟨⟨j, List.mem_cons_self ..⟩, _, rfl⟩
      · simp [Res.ok_bind, Res.pure_eq] at h
    | trap c =>
      rcases ih with ⟨hn, h⟩ | ⟨hx, msg, h⟩ <;> simp [Res.trap_bind] at h
    | stuck m =>
      rcases ih with ⟨hn, h⟩ | ⟨hx, msg, h⟩
      · simp [Res.stuck_bind] at h
      · obtain ⟨i, hi⟩ := hx
        cases a <;> exact .inr ⟨⟨i, List.mem_cons_of_mem _ hi⟩, _, rfl⟩

theorem tryHandler_inv {d : TryDest} {base : ValueId} {bc : BlockCall}
    (h : tryHandler d base = .ok bc) :
    bc = { block := d.block, args := d.args.map (exnId base) } := by
  obtain ⟨blk, l⟩ := d
  rcases tryHandler_cases base blk l with ⟨-, h'⟩ | ⟨-, msg, h'⟩
  · rw [h'] at h; cases h; rfl
  · rw [h'] at h; cases h

theorem tryHandler_of_noRet {d : TryDest} {base : ValueId} (h : ∀ i, TryArg.ret i ∉ d.args) :
    tryHandler d base = .ok { block := d.block, args := d.args.map (exnId base) } := by
  obtain ⟨blk, l⟩ := d
  rcases tryHandler_cases base blk l with ⟨-, h'⟩ | ⟨⟨i, hi⟩, -⟩
  · exact h'
  · exact absurd hi (h i)

theorem tryHandler_ne_trap (d : TryDest) (base : ValueId) (c : TrapCode) :
    tryHandler d base ≠ .trap c := by
  obtain ⟨blk, l⟩ := d
  rcases tryHandler_cases base blk l with ⟨-, h'⟩ | ⟨-, msg, h'⟩ <;> rw [h'] <;>
    exact fun h => by cases h

theorem expandExn_noRet {C : Ctx} :
    ∀ {as : List TryArg} {ps : List (ValueId × Ty)} {as' : List TryArg},
    expandExn C as ps = some as' → ∀ i, TryArg.ret i ∉ as'
  | [], [], as', h, i, hi => by simp [expandExn] at h; subst h; simp at hi
  | .val v :: as, (_, t) :: ps, as', h, i, hi => by
    simp only [expandExn] at h
    split at h
    · split at h
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
        simp only [List.cons_append, List.nil_append, List.mem_cons, reduceCtorEq, false_or] at hi
        exact expandExn_noRet hr i hi
      · cases h
    · split at h
      · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
        simp only [List.mem_cons, reduceCtorEq, false_or] at hi
        exact expandExn_noRet hr i hi
      · cases h
  | .exn j :: as, (_, t) :: ps, as', h, i, hi => by
    simp only [expandExn] at h
    split at h
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [List.mem_cons, reduceCtorEq, false_or] at hi
      exact expandExn_noRet hr i hi
    · cases h
  | .ret _ :: _, _ :: _, _, h, _, _ => by simp [expandExn] at h
  | [], _ :: _, _, h, _, _ => by simp [expandExn] at h
  | _ :: _, [], _, h, _, _ => by simp [expandExn] at h

/-- **The handler arguments.** In the source registers `ρ1` (the values of `f` as in `ρ`, the
payload at `base + i`) and the target registers `ρ1'` (the values below `base'` as in `ρ'`, the
payload at `base' + i`), the arguments `expandExn` expands are the source arguments split by
the parameters (`BExp`). -/
theorem expandExn_holds {C : Ctx} {ρ ρ' ρ1 ρ1' : Regs} (hV : VRel C ρ ρ') {pay : List Val}
    (hpay : 2 ≤ pay.length) {base base' : ValueId}
    (h1 : ∀ v, v < C.T0 → ρ1 v = ρ v) (h1r : ∀ i, i < pay.length → ρ1 (base + i) = pay[i]?)
    (h1' : ∀ a, a < base' → ρ1' a = ρ' a) (h1r' : ∀ j, j < pay.length → ρ1' (base' + j) = pay[j]?)
    (hcomp : ∀ v a b, C.pair v = some (a, b) → a < base' ∧ b < base') (hT : C.T0 ≤ base') :
    ∀ {as as' : List TryArg} {ps : List (ValueId × Ty)} {vals : List Val},
    expandExn C as ps = some as' → (∀ v, TryArg.val v ∈ as → v < C.T0) →
    Holds ρ1 (as.map (exnId base)) vals →
    ∃ vals', Holds ρ1' (as'.map (exnId base')) vals' ∧ BExp ps vals vals'
  | [], as', [], vals, h, _, hv => by
    simp only [expandExn, Option.some.injEq] at h
    subst h
    cases vals with
    | nil => exact ⟨[], trivial, trivial⟩
    | cons => exact hv.elim
  | .val v :: as, as', (q, t) :: ps, vals, h, hlt, hv => by
    cases vals with
    | nil => exact hv.elim
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := hv
      have hv0 : v < C.T0 := hlt v (List.mem_cons_self ..)
      have hlt' : ∀ w, TryArg.val w ∈ as → w < C.T0 := fun w hw => hlt w (List.mem_cons_of_mem _ hw)
      simp only [exnId] at hx
      rw [h1 v hv0] at hx
      simp only [expandExn] at h
      by_cases ht : t = .i128
      · simp only [show (t == Ty.i128) = true from by simp [ht], ite_true] at h
        split at h
        · rename_i a b hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h2, h3⟩ :=
            expandExn_holds hV hpay h1 h1r h1' h1r' hcomp hT hr hlt' hxs
          obtain ⟨l, hh, rfl, ha, hb⟩ := hV.get_pair hv0 hp hx
          obtain ⟨hab, hbb⟩ := hcomp v a b hp
          refine ⟨⟨.i64, l⟩ :: ⟨.i64, hh⟩ :: vals', ⟨?_, ?_, h2⟩, ?_⟩
          · simp only [exnId]; rw [h1' a hab, ha]
          · simp only [exnId]; rw [h1' b hbb, hb]
          · simp only [BExp, ht, ite_true]
            exact ⟨_, _, _, rfl, ⟨l, hh, rfl, rfl, rfl⟩, h3⟩
        · cases h
      · simp only [show (t == Ty.i128) = false from by simp [ht], Bool.false_eq_true, ite_false] at h
        split at h
        · rename_i hp
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨vals', h2, h3⟩ :=
            expandExn_holds hV hpay h1 h1r h1' h1r' hcomp hT hr hlt' hxs
          refine ⟨x :: vals', ⟨?_, h2⟩, ?_⟩
          · simp only [exnId]; rw [h1' v (Nat.lt_of_lt_of_le hv0 hT), hV.get_plain hv0 hp hx]
          · simp only [BExp, ht, ite_false]
            exact ⟨_, rfl, h3⟩
        · cases h
  | .exn i :: as, as', (q, t) :: ps, vals, h, hlt, hv => by
    cases vals with
    | nil => exact hv.elim
    | cons x xs =>
      obtain ⟨hx, hxs⟩ := hv
      have hlt' : ∀ w, TryArg.val w ∈ as → w < C.T0 := fun w hw => hlt w (List.mem_cons_of_mem _ hw)
      simp only [expandExn] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
        obtain ⟨ht, hi2⟩ := hc
        obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨vals', h2, h3⟩ := expandExn_holds hV hpay h1 h1r h1' h1r' hcomp hT hr hlt' hxs
        have hi : i < pay.length := by omega
        simp only [exnId] at hx
        rw [h1r i hi] at hx
        refine ⟨x :: vals', ⟨?_, h2⟩, ?_⟩
        · simp only [exnId]; rw [h1r' i hi, hx]
        · simp only [BExp, ht, ite_false]
          exact ⟨_, rfl, h3⟩
      · cases h
  | .ret _ :: _, _, _ :: _, _, h, _, _ => by simp [expandExn] at h
  | [], _, _ :: _, _, h, _, _ => by simp [expandExn] at h
  | _ :: _, _, [], _, h, _, _ => by simp [expandExn] at h

/-! ## A `try_call` whose callee unwinds -/

theorem tryCallRaise_inv {env : XEnv} {p : Program} {m : Mem} {fr : Frame} {fn : FnRef}
    {args : List ValueId} {et : ExnTable} {r : Exn × Mem}
    (h : tryCallRaise env p m fr fn args et = some r) : callRaise env p m fr fn args = some r := by
  unfold tryCallRaise at h
  split at h
  · exact h
  · cases h

theorem catch?_vals {et : ExnTable} {e : Exn} {d : TryDest} (h : et.catch? e = some d) :
    ∀ v, TryArg.val v ∈ d.args → v ∈ et.vals := by
  intro v hv
  unfold ExnTable.catch? at h
  obtain ⟨it, hit, hd⟩ := List.exists_of_findSome?_eq_some h
  have hvd : v ∈ d.vals := val_mem_vals hv
  simp only [ExnTable.vals, List.mem_append, List.mem_flatMap]
  refine .inr ⟨it, hit, ?_⟩
  cases it with
  | tag n d0 =>
    simp only at hd
    split at hd
    · cases hd; exact hvd
    · cases hd
  | default d0 => simp only [Option.some.injEq] at hd; subst hd; exact hvd
  | context _ => cases hd

theorem raiseAt_jump {env : XEnv} {p : Program} {fr : Frame} {m : Mem} {bc : BlockCall}
    (hb : fr.body = []) (ht : fr.term = .jump bc) : raiseAt? env p ⟨fr, [], m⟩ = none := by
  simp [raiseAt?, hb, ht]

/-- **A `try_call` whose callee unwinds**: the target's callee unwinds with the same exception;
the tables catch it at related handlers or not at all (`exnOk`): both frames are left, or both
continue at the handler blocks, related (after the pending jumps). -/
theorem sim_try_raise {C : Ctx} (hG : Good C) (hx : exnOk C.f C.g C.cert = true) {env : XEnv}
    {p p' : Program} (hE : EnvOkX env C p p') {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr')
    (hIC : InCode C.g fr') (hb : fr.body = []) {fn : FnRef} {args : List ValueId} {et : ExnTable}
    (ht : fr.term = .tryCall fn args et) {x : Exn} {m1 : Mem}
    (hr : tryCallRaise env p m fr fn args et = some (x, m1)) :
    (stepX env p ⟨⟨fr, [], m⟩, []⟩ = .unwound x (leftMem fr m1) ∧
      stepX env p' ⟨⟨fr', [], m⟩, []⟩ = .unwound x (leftMem fr m1)) ∨
    (∃ msg, stepX env p ⟨⟨fr, [], m⟩, []⟩ = .stuck msg) ∨
    ∃ fr1 fr1', stepX env p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨fr1, [], m1⟩, []⟩ ∧
      stepX env p' ⟨⟨fr', [], m⟩, []⟩ = .next ⟨⟨fr1', [], m1⟩, []⟩ ∧
      ((∃ msg, stepX env p ⟨⟨fr1, [], m1⟩, []⟩ = .stuck msg) ∨
        ∃ fr2 fr2', stepX env p ⟨⟨fr1, [], m1⟩, []⟩ = .next ⟨⟨fr2, [], m1⟩, []⟩ ∧
          stepX env p' ⟨⟨fr1', [], m1⟩, []⟩ = .next ⟨⟨fr2', [], m1⟩, []⟩ ∧
          FRel C fr2 fr2' ∧ InCode C.g fr2') := by
  obtain ⟨B0, hB0, -, hterm⟩ := hR.blk
  have hlt : ∀ y ∈ args ++ et.vals, y < C.T0 := fun y hy =>
    term_ops_lt hG hB0 (by rw [← hterm, ht]; exact hy)
  have hcode := hR.code
  rw [hb, ht] at hcode
  simp only [codeOk] at hcode
  cases ht' : fr'.term
  all_goals first | (rw [ht'] at hcode; simp [termOk] at hcode; done) | skip
  rename_i fn' args' et'
  rw [ht'] at hcode
  have hcode0 := hcode
  obtain ⟨hts, hfnn, hsig, hblk, hne, hT0f, hT0g, hzg, hcg, e, d', B, s', gs, rg, he, hd', hB,
    hs', hgs, hrg, hfn', htyp, htyr, hexp, hexpT⟩ := termOk_tryCall hcode
  rw [hfnn] at ht' hcode hcode0
  -- the handler tables are related
  have hitems : itemsOk C et.items et'.items = true := by
    obtain ⟨-, hpos⟩ := hIC
    rcases hpos with ⟨B0', hB0', hterm'⟩ | ⟨-, bc, hj⟩
    · rw [hts] at hcode0
      exact exnOk_items hx hB0 hB0' (hterm ▸ ht) (hterm' ▸ ht') hcode0
    · rw [ht'] at hj; cases hj
  -- the source's callee
  have hrc := tryCallRaise_inv hr
  obtain ⟨ext, vals, g, hxe, hv, hty, hp, hg, hgo⟩ := callRaise_inv hrc
  rw [hR.func, he] at hxe
  cases hxe
  obtain ⟨gs0, rg0, hgs0, hrg0, hpar', hret'⟩ := sigExp_spec hs'
  rw [hgs] at hgs0; cases hgs0
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp
    (fun y hy => hlt y (List.mem_append_left _ hy)) (getMany_holds hv)
  have hty' : vals'.map (·.ty) = AbiParam.tys s'.params := by
    rw [hpar', AbiParam.tys, ← expRel_tys (groups_spec hgs) hexp' hty]
  have hfe' : fr'.func.extern? fn = some { e with sig := s' } := by rw [hR.func']; exact hfn'
  have hrc' : callRaise env p' m fr' fn args' = some (x, m1) :=
    callRaise_of hfe' (holds_getMany hv') hty' (hE.base.tgt fn _ hfn') hg
      (hE.extX e.name g hg e.sig gs hgs vals vals' m hty hexp' x m1 hgo)
  -- the target's `try_call` raises
  have hd2 : fr'.func.sigDecls.lookup et'.sig = some d' := by rw [hR.func', hsig]; exact hd'
  have hbc2 := tryNormal_of_noExn (base := fr'.func.freshValue) (expandTry_noExn hexpT)
  have hr' : tryCallRaise env p' m fr' fn args' et' = some (x, m1) := by
    simp only [tryCallRaise, hfe', hd2, hbc2, htyp, htyr, Res.ofOption, bind, Res.bind, Res.check,
      beq_self_eq_true, Bool.and_self, ite_true, pure]
    exact hrc'
  have hpend : pendingOf ⟨fr, [], m⟩ = some et := by simp [pendingOf, hb, ht]
  have hpend' : pendingOf ⟨fr', [], m⟩ = some et' := by simp [pendingOf, hts, ht']
  have hstep : stepX env p ⟨⟨fr, [], m⟩, []⟩ = raiseIn ⟨⟨fr, [], m⟩, []⟩ x m1 := by
    simp [stepX, raiseAt?, hb, ht, hr]
  have hstep' : stepX env p' ⟨⟨fr', [], m⟩, []⟩ = raiseIn ⟨⟨fr', [], m⟩, []⟩ x m1 := by
    simp [stepX, raiseAt?, hts, ht', hr']
  rw [hstep, hstep']
  rcases catch?_rel (e := x) hitems with ⟨hn, hn'⟩ | ⟨d, d'', hc, hc', hdo⟩
  · -- nothing catches: both frames are left
    refine .inl ⟨?_, ?_⟩
    · simp [raiseIn, hpend, catchIn, hn, unwindFrom, leftMem]
    · simp [raiseIn, hpend', catchIn, hn', unwindFrom, leftMem, hR.slots]
  -- related handlers
  simp only [destOk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hdo
  obtain ⟨⟨hblkd, hned⟩, hdo⟩ := hdo
  split at hdo
  · rename_i Bh hBh
    simp only [beq_iff_eq] at hdo
    cases hth : tryHandler d fr.func.freshValue with
    | trap c => exact absurd hth (tryHandler_ne_trap _ _ c)
    | stuck msg =>
      refine .inr (.inl ⟨msg, ?_⟩)
      simp [raiseIn, hpend, catchIn, hc, hth, bind, Res.bind, XStepResult.ofRes]
    | ok bc =>
    have hbcE := tryHandler_inv hth
    have hth' := tryHandler_of_noRet (base := fr'.func.freshValue) (expandExn_noRet hdo)
    generalize hbc'e : ({ block := d''.block, args := d''.args.map (exnId fr'.func.freshValue) } :
      BlockCall) = bc' at hth'
    have hpay := hE.arity e.name g hg vals m x m1 hgo
    obtain ⟨ρ1, hs⟩ := setMany_of_len fr.regs
      (rs := (List.range x.payload.length).map (fr.func.freshValue + ·)) (vs := x.payload)
      (by simp)
    obtain ⟨ρ1', hs'⟩ := setMany_of_len fr'.regs
      (rs := (List.range x.payload.length).map (fr'.func.freshValue + ·)) (vs := x.payload)
      (by simp)
    have hfv : fr.func.freshValue = C.f.freshValue := by rw [hR.func]
    have hfv' : fr'.func.freshValue = C.g.freshValue := by rw [hR.func']
    refine .inr (.inr ⟨{ fr with regs := ρ1, body := [], term := .jump bc },
      { fr' with regs := ρ1', body := [], term := .jump bc' }, ?_, ?_, ?_⟩)
    · simp [raiseIn, hpend, catchIn, hc, hth, hs, bind, Res.bind, Res.ofOption, pure,
        XStepResult.ofRes]
    · simp [raiseIn, hpend', catchIn, hc', hth', hs', bind, Res.bind, Res.ofOption, pure,
        XStepResult.ofRes]
    -- the pending jumps
    have hCR := crel_bind hG hR.toCRel hs hs'
      (fun v hv => by have := (mem_range_map hv).1; rw [hfv] at this; omega)
      (fun w hw => fresh_of_ge (base' := C.g.freshValue) hT0g hzg hcg
        (by have := (mem_range_map hw).1; rw [hfv'] at this; exact this))
      [] (.jump bc) [] (.jump bc')
    have hsrc : stepX env p ⟨⟨{ fr with regs := ρ1, body := [], term := .jump bc }, [], m1⟩, []⟩ =
        liftStep ⟨⟨{ fr with regs := ρ1, body := [], term := .jump bc }, [], m1⟩, []⟩
          (StepResult.ofRes (enterBlock { fr with regs := ρ1, body := [], term := .jump bc } bc)
            fun fr2 => .next ⟨fr2, [], m1⟩) := by
      simp only [stepX, raiseAt_jump (env := env) (p := p) (m := m1)
        (fr := { fr with regs := ρ1, body := [], term := .jump bc }) rfl rfl]
      rw [step_term _ _ _ rfl]
      rfl
    have htgt : stepX env p' ⟨⟨{ fr' with regs := ρ1', body := [], term := .jump bc' }, [], m1⟩, []⟩ =
        liftStep ⟨⟨{ fr' with regs := ρ1', body := [], term := .jump bc' }, [], m1⟩, []⟩
          (StepResult.ofRes (enterBlock { fr' with regs := ρ1', body := [], term := .jump bc' } bc')
            fun fr2 => .next ⟨fr2, [], m1⟩) := by
      simp only [stepX, raiseAt_jump (env := env) (p := p') (m := m1)
        (fr := { fr' with regs := ρ1', body := [], term := .jump bc' }) rfl rfl]
      rw [step_term _ _ _ rfl]
      rfl
    rw [hsrc, htgt]
    cases hen : enterBlock { fr with regs := ρ1, body := [], term := .jump bc } bc with
    | trap c => exact absurd hen (enterBlock_not_trap _ _ c)
    | stuck msg => exact .inl ⟨msg, by simp [liftStep]⟩
    | ok fr2 =>
    obtain ⟨fr2', hen', hR2⟩ := enter_sim_vals hG hCR (bc' := bc')
      (by rw [← hbc'e, hbcE]; exact hblkd) (by rw [hbcE]; exact hned)
      (fun B1 vals1 hB1 hv1 => by
        rw [← hbc'e]
        rw [hbcE] at hB1 hv1
        rw [hBh] at hB1
        cases hB1
        exact expandExn_holds hR.vrel hpay
          (base := fr.func.freshValue) (base' := fr'.func.freshValue)
          (fun v hv => setMany_other hs fun hm => by
            have := (mem_range_map hm).1; rw [hfv] at this
            exact absurd hv (Nat.not_lt.mpr (Nat.le_trans hT0f this)))
          (fun i hi => setMany_get hs (range_map_nodup _ _) (getElem?_range_map hi))
          (fun a ha => setMany_other hs' fun hm => absurd ha (Nat.not_lt.mpr (mem_range_map hm).1))
          (fun j hj => setMany_get hs' (range_map_nodup _ _) (getElem?_range_map hj))
          (fun v a b hp => by
            obtain ⟨ha, hb⟩ := mem_comps hp
            rw [hfv']; exact ⟨hcg a ha, hcg b hb⟩)
          (by rw [hfv']; exact hT0g) hdo
          (fun v hv => hlt v (List.mem_append_right _ (catch?_vals hc v hv))) hv1) hen
    refine .inr ⟨fr2, fr2', by simp [liftStep], by simp [hen', liftStep], hR2, ?_⟩
    obtain ⟨h1, B2, hB2, h2⟩ := enterBlock_next hen'
    refine ⟨h1.trans hR.func', .inl ⟨B2, ?_, h2⟩⟩
    rw [hR.func'] at hB2
    exact hB2
  · cases hdo

/-! ## Runs -/

/-- What the target run with unwinding does for an outcome of the source run with unwinding. -/
def XSimOut (C : Ctx) (env : XEnv) (p' : Program) (fr' : Frame) (m : Mem) : XOutcome → Prop
  | .returned vals m1 => ∃ vals', ExpRel C.rg vals vals' ∧
      ∃ k, runLoopX env p' k ⟨⟨fr', [], m⟩, []⟩ = .returned vals' m1
  | .trapped c => ∃ k, runLoopX env p' k ⟨⟨fr', [], m⟩, []⟩ = .trapped c
  | .unwound e m1 => ∃ k, runLoopX env p' k ⟨⟨fr', [], m⟩, []⟩ = .unwound e m1
  | .stuck _ | .outOfFuel => True

theorem XSimOut.pre {C : Ctx} {env : XEnv} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem} {k : Nat}
    (hk : ∀ n, runLoopX env p' (n + k) ⟨⟨fr', [], m⟩, []⟩ = runLoopX env p' n ⟨⟨fr1', [], m1⟩, []⟩)
    {o : XOutcome} (h : XSimOut C env p' fr1' m1 o) : XSimOut C env p' fr' m o := by
  cases o with
  | returned vals m2 =>
    obtain ⟨vals', hv, j, hj⟩ := h
    exact ⟨vals', hv, j + k, by rw [hk, hj]⟩
  | trapped c =>
    obtain ⟨j, hj⟩ := h
    exact ⟨j + k, by rw [hk, hj]⟩
  | unwound e m2 =>
    obtain ⟨j, hj⟩ := h
    exact ⟨j + k, by rw [hk, hj]⟩
  | stuck _ => trivial
  | outOfFuel => trivial

/-- A source step without a raising callee, matched by target steps (`SimOut`), continued by
the induction hypothesis `ih` at the next state. -/
theorem xsim_of_simOut {C : Ctx} (hnr : ∀ B ∈ C.g.blocks, ∀ fn args, B.term ≠ .returnCall fn args)
    {env : XEnv} {p p' : Program} {fr fr' : Frame} {m : Mem} {n : Nat}
    (hst : stepX env p ⟨⟨fr, [], m⟩, []⟩ = liftStep ⟨⟨fr, [], m⟩, []⟩ (step env.toEnv p ⟨fr, [], m⟩))
    (hS : S.SimOut C env.toEnv p' fr' m (step env.toEnv p ⟨fr, [], m⟩)) (hIC : InCode C.g fr')
    (ih : ∀ fr1 fr1' m1, FRel C fr1 fr1' → InCode C.g fr1' → MemBounded m1 →
      stepX env p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨fr1, [], m1⟩, []⟩ →
      XSimOut C env p' fr1' m1 (runLoopX env p n ⟨⟨fr1, [], m1⟩, []⟩)) :
    XSimOut C env p' fr' m (runLoopX env p (n + 1) ⟨⟨fr, [], m⟩, []⟩) := by
  cases hr : step env.toEnv p ⟨fr, [], m⟩ with
  | next s1 =>
    rw [hr] at hS hst
    obtain ⟨sf, scl, sm⟩ := s1
    obtain ⟨hcl, hM1, fr1', hR1, hT1⟩ := hS
    simp only at hcl hM1 hR1 hT1
    subst hcl
    have hst' : stepX env p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨sf, [], sm⟩, []⟩ := by
      rw [hst]; simp [liftStep]
    rw [runLoopX_next hst']
    obtain ⟨k, hk⟩ := tstep_runLoopX hT1
    exact XSimOut.pre hk (ih sf fr1' sm hR1 (tstep_inCode hnr hT1 hIC) hM1 hst')
  | done vals m1 =>
    rw [hr] at hS hst
    obtain ⟨vals', hv, k, hk⟩ := hS
    have : runLoopX env p (n + 1) ⟨⟨fr, [], m⟩, []⟩ = .returned vals m1 := by
      rw [Clif.runLoopX, hst]; rfl
    rw [this]
    exact ⟨vals', hv, k, runLoopX_of_returned k ⟨⟨fr', [], m⟩, []⟩ hk⟩
  | trapped c =>
    rw [hr] at hS hst
    obtain ⟨k, hk⟩ := hS
    have : runLoopX env p (n + 1) ⟨⟨fr, [], m⟩, []⟩ = .trapped c := by
      rw [Clif.runLoopX, hst]; rfl
    rw [this]
    exact ⟨k, runLoopX_of_trapped k ⟨⟨fr', [], m⟩, []⟩ hk⟩
  | stuck msg =>
    rw [hr] at hst
    have : runLoopX env p (n + 1) ⟨⟨fr, [], m⟩, []⟩ = .stuck msg := by
      rw [Clif.runLoopX, hst]; rfl
    rw [this]
    trivial

theorem runLoopX_unwound {env : XEnv} {p : Program} {xs : XState} {e : Exn} {m : Mem}
    (h : stepX env p xs = .unwound e m) (n : Nat) : runLoopX env p (n + 1) xs = .unwound e m := by
  rw [Clif.runLoopX, h]

theorem runLoopX_stuck {env : XEnv} {p : Program} {xs : XState} {msg : String}
    (h : stepX env p xs = .stuck msg) (n : Nat) : runLoopX env p (n + 1) xs = .stuck msg := by
  rw [Clif.runLoopX, h]

/-- The memory an extern leaves when it unwinds keeps valid ranges below `2^64`. -/
theorem memBounded_raise {env : XEnv} (hK : EnvKeepsAllocsX env) {p : Program} {m : Mem}
    {fr : Frame} {fn : FnRef} {args : List ValueId} {x : Exn} {m1 : Mem}
    (h : callRaise env p m fr fn args = some (x, m1)) (hM : MemBounded m) : MemBounded m1 := by
  obtain ⟨ext, vals, g, -, -, -, -, hg, hgo⟩ := callRaise_inv h
  exact memBounded_of_allocs (hK _ g hg vals m x m1 hgo) hM

/-- **Runs with unwinding.** From related frames (the target in `g`'s code), an outcome of the
source run with unwinding within `n` steps is one of the target's: a return with the values
expanded, a trap, an exception leaving the function with the same memory. -/
theorem sim_runX {C : Ctx} (hG : Good C) (hx : exnOk C.f C.g C.cert = true)
    (hold : indOldB C.f = true) {env : XEnv}
    {p p' : Program} (hE : EnvOkX env C p p') :
    ∀ (n : Nat) (fr fr' : Frame) (m : Mem), FRel C fr fr' → InCode C.g fr' → MemBounded m →
      NoMemTrapX env p ⟨fr, [], m⟩ → NoIndInternalX env p C.f ⟨fr, [], m⟩ →
      XSimOut C env p' fr' m (runLoopX env p n ⟨⟨fr, [], m⟩, []⟩) := by
  have hnr : ∀ B ∈ C.g.blocks, ∀ fn args, B.term ≠ .returnCall fn args :=
    fun B hB => exnOk_noReturnCall hx hB
  have hE2 := hE.base.two
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro fr fr' m hR hIC hM hT hI
  cases n with
  | zero => trivial
  | succ n =>
  have ihn : ∀ fr1 fr1' m1, FRel C fr1 fr1' → InCode C.g fr1' → MemBounded m1 →
      stepX env p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨fr1, [], m1⟩, []⟩ →
      XSimOut C env p' fr1' m1 (runLoopX env p n ⟨⟨fr1, [], m1⟩, []⟩) :=
    fun fr1 fr1' m1 hR1 hIC1 hM1 hs => ih n (by omega) fr1 fr1' m1 hR1 hIC1 hM1 (hT.next hs) (hI.next hs)
  cases hra : raiseAt? env p ⟨fr, [], m⟩ with
  | none =>
    have hst : stepX env p ⟨⟨fr, [], m⟩, []⟩ =
        liftStep ⟨⟨fr, [], m⟩, []⟩ (step env.toEnv p ⟨fr, [], m⟩) := by
      simp [stepX, hra]
    have hT0 := hT _ (.refl _)
    have hI0 := hI _ (.refl _)
    by_cases htc : fr.body = [] ∧ ∃ fn args et, fr.term = .tryCall fn args et
    · obtain ⟨hb, fn, args, et, ht⟩ := htc
      rcases S.sim_try hG hE2 hR hM hb ht with hS | ⟨s1, hs1, hcl, hM1, fr1', hT1, hS2⟩
      · exact xsim_of_simOut hnr hst hS hIC ihn
      · obtain ⟨sf, scl, sm⟩ := s1
        simp only at hcl hM1 hT1 hS2
        subst hcl
        have hst1 : stepX env p ⟨⟨fr, [], m⟩, []⟩ = .next ⟨⟨sf, [], sm⟩, []⟩ := by
          rw [hst, hs1]; simp [liftStep]
        rw [runLoopX_next hst1]
        obtain ⟨k, hk⟩ := tstep_runLoopX hT1
        refine XSimOut.pre hk ?_
        -- the pending jump
        have hshape : sf.body = [] ∧ ∃ bc, sf.term = .jump bc := by
          rw [step_term _ _ _ hb] at hs1
          simp only [ht] at hs1
          exact (stepTryCall_next hs1 rfl).2
        obtain ⟨hb1, bc, hj1⟩ := hshape
        cases n with
        | zero => trivial
        | succ n =>
        have hst2 : stepX env p ⟨⟨sf, [], sm⟩, []⟩ =
            liftStep ⟨⟨sf, [], sm⟩, []⟩ (step env.toEnv p ⟨sf, [], sm⟩) := by
          simp [stepX, raiseAt_jump (env := env) (p := p) (m := sm) hb1 hj1]
        exact xsim_of_simOut hnr hst2 hS2 (tstep_inCode hnr hT1 hIC)
          fun fr2 fr2' m2 hR2 hIC2 hM2 hs2 => ih n (by omega) fr2 fr2' m2 hR2 hIC2 hM2
            ((hT.next hst1).next hs2) ((hI.next hst1).next hs2)
    · exact xsim_of_simOut hnr hst
        (S.step_sim_out hG hE2 hold hR hM hT0 hI0 fun hb fn args et h => htc ⟨hb, fn, args, et, h⟩)
        hIC ihn
  | some r =>
    obtain ⟨x, m1⟩ := r
    cases hb : fr.body with
    | cons st rest =>
      have hra' := hra
      simp only [raiseAt?, hb] at hra'
      split at hra'
      · rename_i fn args hi
        obtain ⟨h1, h2⟩ := sim_call_raise hG hE hR hb hi hra'
        rw [runLoopX_unwound h1]
        exact ⟨1, runLoopX_unwound h2 0⟩
      · rename_i sig callee args hi
        obtain ⟨h1, h2⟩ := sim_callInd_raise hG hold hE hR hb hi hra'
        rw [runLoopX_unwound h1]
        exact ⟨1, runLoopX_unwound h2 0⟩
      · cases hra'
    | nil =>
      have hra' := hra
      simp only [raiseAt?, hb] at hra'
      have hcode := hR.code
      rw [hb] at hcode
      simp only [codeOk] at hcode
      split at hra'
      · rename_i fn args ht
        rw [ht] at hcode
        cases ht' : fr'.term <;> rw [ht'] at hcode <;> simp [termOk] at hcode
      · rename_i fn args et ht
        have hM1 := memBounded_raise hE.keepX (tryCallRaise_inv hra') hM
        rcases sim_try_raise hG hx hE hR hIC hb ht hra' with ⟨h1, h2⟩ | ⟨msg, h1⟩ |
          ⟨fr1, fr1', h1, h2, h3⟩
        · rw [runLoopX_unwound h1]
          exact ⟨1, runLoopX_unwound h2 0⟩
        · rw [runLoopX_stuck h1]; trivial
        · rw [runLoopX_next h1]
          refine XSimOut.pre (k := 1) (fun q => runLoopX_next h2 q) ?_
          cases n with
          | zero => trivial
          | succ n =>
          rcases h3 with ⟨msg, h3⟩ | ⟨fr2, fr2', h3, h4, hR2, hIC2⟩
          · rw [runLoopX_stuck h3]; trivial
          · rw [runLoopX_next h3]
            refine XSimOut.pre (k := 1) (fun q => runLoopX_next h4 q) ?_
            exact ih n (by omega) fr2 fr2' m1 hR2 hIC2 hM1 ((hT.next h1).next h3)
              ((hI.next h1).next h3)
      · rename_i callee args et ht
        exact (S.frel_not_tryInd hR hold callee args et ht).elim
      · cases hra'

/-- **The refinement theorem of `Opt.Legal.check` with unwinding.** For a legalisation `g` of
`f` accepted by `check` and by the handler-edge check `exnOk`: from entry states of `f` on `args`
and of `g` on `args'` (the arguments expanded by the ABI groups of `f`'s parameters; same slots
and memory), whenever the run of `f` with unwinding returns within `fuel` steps, the run of `g`
with unwinding returns the values expanded by the ABI groups of `f`'s returns with the same
memory; whenever it traps, `g`'s traps with the same code; whenever an exception leaves `f`,
the same exception leaves `g` with the same memory. Premises: `EnvOkX`, valid ranges below
`2^64`, no load/store trap and no indirect call of a function of `p` in the source run with
unwinding. -/
theorem check_refinesX {C : Ctx} (hc : check C.f C.g C.cert = true)
    (hx : exnOk C.f C.g C.cert = true)
    {env : XEnv} {p p' : Program} (hE : EnvOkX env C p p') {b b' : Block}
    (hb : C.f.entry? = some b) (hb' : C.g.entry? = some b') {args args' : List Val}
    {fr0 fr0' : Frame} {m : Mem}
    (h1 : fr0.func = C.f) (h2 : fr0.body = b.body) (h3 : fr0.term = b.term)
    (h4 : b.params.map (·.2) = args.map (·.ty))
    (h5 : Regs.empty.setMany (b.params.map (·.1)) args = some fr0.regs)
    (h1' : fr0'.func = C.g) (h2' : fr0'.body = b'.body) (h3' : fr0'.term = b'.term)
    (h5' : Regs.empty.setMany (b'.params.map (·.1)) args' = some fr0'.regs)
    (hsl : fr0'.slots = fr0.slots)
    (hexp : ExpRel ((groups C.f.sig.params).getD []) args args')
    (hM : MemBounded m) (hT : NoMemTrapX env p ⟨fr0, [], m⟩)
    (hI : NoIndInternalX env p C.f ⟨fr0, [], m⟩) (fuel : Nat) :
    (∀ vals m1, runLoopX env p fuel ⟨⟨fr0, [], m⟩, []⟩ = .returned vals m1 →
      ∃ vals', ExpRel ((groups C.f.sig.returns).getD []) vals vals' ∧
        ∃ k, runLoopX env p' k ⟨⟨fr0', [], m⟩, []⟩ = .returned vals' m1) ∧
    (∀ c, runLoopX env p fuel ⟨⟨fr0, [], m⟩, []⟩ = .trapped c →
      ∃ k, runLoopX env p' k ⟨⟨fr0', [], m⟩, []⟩ = .trapped c) ∧
    (∀ e m1, runLoopX env p fuel ⟨⟨fr0, [], m⟩, []⟩ = .unwound e m1 →
      ∃ k, runLoopX env p' k ⟨⟨fr0', [], m⟩, []⟩ = .unwound e m1) := by
  have hG : Good C := check_good hc
  obtain ⟨b0, bs, b0', bs', hf, hg, -, hok, -⟩ := hG.blocks
  simp only [Function.entry?, hf, List.head?_cons, Option.some.injEq] at hb
  simp only [Function.entry?, hg, List.head?_cons, Option.some.injEq] at hb'
  subst hb hb'
  have hBmem : b0 ∈ C.f.blocks := by rw [hf]; exact List.mem_cons_self ..
  simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ite_true] at hok
  obtain ⟨⟨-, hnd'⟩, hok⟩ := hok
  split at hok
  · rename_i gs z rest hgs hbody'
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hep, rfl⟩, hcode⟩ := hok
    simp only [hgs, Option.getD_some] at hexp
    obtain ⟨hty', hbind, hcov⟩ := entry_bind hep hexp h4.symm
    have hnd := params_nodup hG.defs hBmem
    have H0 := holds_setMany hnd h5
    have H0' := holds_setMany hnd' h5'
    -- the target's first step: the pad zero
    have hz : lstep fr0' m = .next { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } m := by
      have hb0 : fr0'.body = C.zeroStmt :: rest := by rw [h2', hbody']
      rw [lstep_eval (m1 := m) (vals := [zeroVal]) hb0 (fun _ _ h => by cases h) rfl rfl]
    have hzT : S.TStep env.toEnv p' fr0' m
        { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } m :=
      S.TStep.of_lstar (.single hz)
    -- parameters of the target that are values of `f` are the source parameters
    have hpar : ∀ v, v < C.T0 → v ∉ b0.params.map (·.1) → v ∉ b0'.params.map (·.1) := by
      intro v hv hvn hv'
      rcases hcov v hv' with hf' | ⟨u, hu, hvu⟩
      · have := (fresh_spec hf').1; vomega
      · cases hpu : C.pair u with
        | none =>
          simp only [img, hpu, List.mem_singleton] at hvu
          exact hvn (hvu ▸ hu)
        | some ab =>
          obtain ⟨a, b⟩ := ab
          obtain ⟨ha, hb, -⟩ := hG.pair_facts hpu
          simp only [img, hpu, List.mem_cons, List.mem_nil_iff, or_false] at hvu
          rcases hvu with rfl | rfl <;> vomega
    have hR : FRel C fr0 { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } := by
      refine ⟨⟨h1, h1', hsl, ?_, ?_, ?_, by simp⟩, ⟨b0, hBmem, by rw [h2]; exact List.suffix_refl _, h3⟩, ?_⟩
      · intro v x hv hx
        have hvp : v ∈ b0.params.map (·.1) := by
          refine Classical.byContradiction fun hn => ?_
          rw [setMany_other h5 hn] at hx; cases hx
        refine (hbind H0 H0' hnd v hvp x hx).congr fun w hw => ?_
        simp only
        rw [Regs.set_other _ _ fun h => zero_not_img hG hv (by rw [← h]; exact hw)]
      · intro v hv hp
        simp only
        have hvz : v ≠ C.zero := fun h => by have := hG.zero_ge; vomega
        rw [Regs.set_other _ _ hvz]
        by_cases hvp : v ∈ b0.params.map (·.1)
        · obtain ⟨x, hx⟩ := holds_mem H0 v hvp
          have := hbind H0 H0' hnd v hvp x hx
          rw [RelV.plain hp] at this
          rw [this, hx]
        · rw [setMany_other h5 hvp, setMany_other h5' (hpar v hv hvp)]
      · exact srcInv_enter hG.defs hBmem (fun _ _ h => by cases h) h4.symm h5
      · simp only
        rw [h2, h3, h3']
        exact hcode
    have hIC : InCode C.g { fr0' with regs := fr0'.regs.set C.zero zeroVal, body := rest } := by
      refine ⟨h1', .inl ⟨b0', ?_, h3'⟩⟩
      rw [hg]; exact List.mem_cons_self ..
    have hS := sim_runX hG hx (indOldB_of_check hc) hE fuel fr0 _ m hR hIC hM hT hI
    obtain ⟨k0, hk0⟩ := tstep_runLoopX (env := env) hzT
    have hS' := XSimOut.pre hk0 hS
    refine ⟨fun vals m1 h => ?_, fun c h => ?_, fun e m1 h => ?_⟩
    · rw [h] at hS'; exact hS'
    · rw [h] at hS'; exact hS'
    · rw [h] at hS'; exact hS'
  · cases hok


end Opt.Legal.X
