module

public import FV.Clif.Run

@[expose] public section

/-!
# `Clif.runX`: `Clif.run` with unwinding (S10b, `docs/plans/unwinding.md`)

Cranelift's `try_call` (`cranelift/codegen/meta/src/shared/instructions.rs`): "On exceptional
return, look up the thrown exception tag in the provided exception table; if the tag matches
one of the targets, branch to the matching target with the exception payload values available
as `exnN` block arguments. If no tag matches, then propagate the exception up the stack. It is
the Cranelift embedder's responsibility to define the meaning of tags."

`Clif.run` has no unwinding (`Clif.stepTryCall`: only the normal return). This module adds it,
**without changing `Clif.run`**: `XEnv`'s externs may end `unwound e mem` (`XOutcome`), and
`stepX` raises the exception at the call that unwound:

* at a `try_call`/`try_call_indirect` whose exception table has a handler catching `e`
  (`ExnTable.catch?`: the first `tagN` item with `e.catches N`, or a `default` item; `context`
  items are skipped), the frame continues at that handler: the payload is bound to the fresh
  values `freshValue + i` and the pending `jump` passes them as `exnN` (`tryHandler`), the
  normal return's two-step shape (`stepTryCall`);
* otherwise the frame is left (its stack slots freed, `Mem.leave`, as `returnValues` does) and
  the exception propagates into the caller: a caller suspended at a `try_call` of a function of
  the program consults that `try_call`'s table (`XState.tries`) the same way, a caller
  suspended at a plain `call` is left too; when no frame is left the run ends `unwound e mem`.

Every other step is `Clif.step env.toEnv` (`XEnv.toEnv`: an `unwound` extern is `stuck` there).

The tag matching (`Exn.catches`) and the payload are the embedder's: for Cranelift's own
`test run` runner (`__cranelift_throw`, the native oracle `rust/crates/clif-throw-native`), a
throw with tag `t` is caught by `tag t` and `default` handlers and carries two payload words;
for cg_clif under Rust's personality, every Rust panic is caught by tag 0 (cleanup) and tag 1
(catch-all) handlers, with payload `[exception object, 0]` (S10d).

Theorems: the old semantics is the restriction to runs where no extern unwinds:
`runLoopX_of_returned` / `runLoopX_of_trapped` (a `returned`/`trapped` run of `Clif.runLoop
env.toEnv` is the same outcome of `runLoopX env`), `runLoopX_toX` (for an environment of
`Clif.run`, `runLoopX` is `runLoop`).
-/

namespace Clif

/-- An exception in flight: which handler tags catch it (the embedder's matching), and the
payload values a handler receives as `exn0`, `exn1`, …. -/
structure Exn where
  catches : Nat → Bool
  payload : List Val

/-- Outcome of an extern or a run with unwinding. `unwound e mem`: the exception `e`
propagated out of the run's bottom frame (its stack slots freed). -/
inductive XOutcome where
  | returned (vals : List Val) (mem : Mem)
  | unwound (e : Exn) (mem : Mem)
  | trapped (code : TrapCode)
  | stuck (msg : String)
  | outOfFuel
  deriving Inhabited

/-- The returned values, if the outcome is `returned`. -/
def XOutcome.returnedVals? : XOutcome → Option (List Val)
  | .returned vals _ => some vals
  | _ => none

/-- The payload of the exception, if the outcome is `unwound`. -/
def XOutcome.unwoundPayload? : XOutcome → Option (List Val)
  | .unwound e _ => some e.payload
  | _ => none

/-- Forget unwinding: `unwound` is `stuck` (what `Clif.run` does at a callee that unwinds). -/
def XOutcome.toOutcome : XOutcome → Outcome
  | .returned vals mem => .returned vals mem
  | .unwound _ _ => .stuck "callee unwound (Clif.run has no unwinding)"
  | .trapped c => .trapped c
  | .stuck m => .stuck m
  | .outOfFuel => .outOfFuel

/-- An outcome of `Clif.run` as one of `runX`. -/
def Outcome.toX : Outcome → XOutcome
  | .returned vals mem => .returned vals mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m
  | .outOfFuel => .outOfFuel

@[simp] theorem Outcome.toX_toOutcome (o : Outcome) : o.toX.toOutcome = o := by
  cases o <;> rfl

/-- `Env` with externs that may unwind. -/
structure XEnv where
  extern : String → Option (List Val → Mem → XOutcome) := fun _ => none
  names : List String := []
  sigOf : String → Option Signature := fun _ => none

/-- The environment of `Clif.run`: an extern that unwinds is `stuck`. -/
def XEnv.toEnv (env : XEnv) : Env where
  extern n := (env.extern n).map fun g vals mem => (g vals mem).toOutcome
  names := env.names
  sigOf := env.sigOf

/-- An environment of `Clif.run` (its externs never unwind). -/
def Env.toX (env : Env) : XEnv where
  extern n := (env.extern n).map fun g vals mem => (g vals mem).toX
  names := env.names
  sigOf := env.sigOf

@[simp] theorem Env.toX_toEnv (env : Env) : env.toX.toEnv = env := by
  cases env with
  | mk ext names sigOf =>
    simp only [XEnv.toEnv, Env.toX, Env.mk.injEq, and_true]
    funext n
    cases ext n <;> simp

/-- The machine state of `runX`: `State`, and for each suspended caller (`s.callers`, same
order) the exception table of the `try_call` it is suspended at (`none` for a plain `call`,
`call_indirect` or a `return_call` chain's caller). -/
structure XState where
  s : State
  tries : List (Option ExnTable)

/-- Result of one step of `runX`. -/
inductive XStepResult where
  | next (xs : XState)
  | done (vals : List Val) (mem : Mem)
  | unwound (e : Exn) (mem : Mem)
  | trapped (code : TrapCode)
  | stuck (msg : String)

def XStepResult.ofRes {α : Type} (r : Res α) (k : α → XStepResult) : XStepResult :=
  match r with
  | .ok a => k a
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-! ## Raising -/

/-- The first handler of `et` that catches `e`. -/
def ExnTable.catch? (et : ExnTable) (e : Exn) : Option TryDest :=
  et.items.findSome? fun
    | .tag n d => if e.catches n then some d else none
    | .default d => some d
    | .context _ => none

/-- A handler successor of a `try_call` as a plain block call, the `i`-th payload value being
value `base + i` (`tryNormal`'s counterpart). -/
def tryHandler (d : TryDest) (base : ValueId) : Res BlockCall := do
  let args ← d.args.mapM fun
    | .val v => pure v
    | .exn i => pure (base + i)
    | .ret _ => .stuck "try_call: return value on an exception edge"
  pure { block := d.block, args }

/-- Frame `fr`, suspended at (or running) a `try_call` with table `et`, resumed by exception
`e`: `none` if no handler catches `e`; else the frame with the payload bound at
`freshValue + i` and the pending `jump` to the handler. -/
def catchIn (fr : Frame) (et : ExnTable) (e : Exn) : Option (Res Frame) :=
  (et.catch? e).map fun d => do
    let base := fr.func.freshValue
    let bc ← tryHandler d base
    let regs ← Res.ofOption "try_call: exception payload arity"
      (fr.regs.setMany ((List.range e.payload.length).map (base + ·)) e.payload)
    pure { fr with regs, body := [], term := .jump bc }

/-- Propagate `e` out of frame `fr` (memory `mem`, the frame's slots not yet freed) into the
suspended `callers` with their pending tables `tries`. -/
def unwindFrom (e : Exn) : Frame → List (Frame × List ValueId) → List (Option ExnTable) → Mem →
    XStepResult
  | fr, [], _, mem => .unwound e ((mem.free (fr.slots.map (·.2))).leave)
  | fr, (c, _) :: cs, t :: ts, mem =>
    let mem := (mem.free (fr.slots.map (·.2))).leave
    match t.bind (catchIn c · e) with
    | some r => XStepResult.ofRes r fun fr' => .next ⟨{ frame := fr', callers := cs, mem }, ts⟩
    | none => unwindFrom e c cs ts mem
  | _, _ :: _, [], _ => .stuck "unwinding: no pending table for a caller"

/-- The exception table of the `try_call` the state is at, if any. -/
def pendingOf (s : State) : Option ExnTable :=
  match s.frame.body, s.frame.term with
  | [], .tryCall _ _ et => some et
  | [], .tryCallIndirect _ _ et => some et
  | _, _ => none

/-- `e` raised by the call the running frame of `xs` is at (memory `mem`): caught by its own
`try_call`, or propagated. -/
def raiseIn (xs : XState) (e : Exn) (mem : Mem) : XStepResult :=
  match (pendingOf xs.s).bind (catchIn xs.s.frame · e) with
  | some r => XStepResult.ofRes r fun fr => .next ⟨{ xs.s with frame := fr, mem }, xs.tries⟩
  | none => unwindFrom e xs.s.frame xs.s.callers xs.tries mem

/-! ## Which steps raise

Each mirrors the corresponding step of `Clif.step` up to the extern's outcome. -/

/-- The extern a `call fnN(args)` of frame `fr` calls unwinds (`stepCall`). -/
def callRaise (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) : Option (Exn × Mem) :=
  match (do
    let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
    let vals ← fr.getMany args
    checkTys s!"arguments of call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
    pure (ext, vals) : Res (ExtFunc × List Val)) with
  | .ok (ext, vals) =>
    match p.func? ext.name with
    | some _ => none
    | none =>
      match env.extern ext.name with
      | some g => match g vals mem with
        | .unwound e m => some (e, m)
        | _ => none
      | none => none
  | _ => none

/-- The extern an indirect call at address `addr` calls unwinds (`callExternAt`). -/
def externAtRaise (env : XEnv) (p : Program) (mem : Mem) (declared : Signature) (addr : Nat)
    (vals : List Val) : Option (Exn × Mem) :=
  match (env.names ++ p.externNames).find? fun n => mem.symbols n == some addr with
  | some name =>
    match env.extern name with
    | some g =>
      if (env.sigOf name).all declared.abiMatch &&
          vals.map (·.ty) == AbiParam.tys declared.params then
        match g vals mem with
        | .unwound e m => some (e, m)
        | _ => none
      else none
    | none => none
  | none => none

/-- A `call_indirect sigN, callee(args)` of frame `fr` calls an extern that unwinds
(`stepCallIndirect`). -/
def callIndRaise (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (sig : Nat)
    (callee : ValueId) (args : List ValueId) : Option (Exn × Mem) :=
  match (do
    let declared ← Res.ofOption s!"unknown signature sig{sig}" (fr.func.sigDecls.lookup sig)
    let cv ← fr.get callee
    let cv64 ← Res.ofOption "call_indirect: callee is not i64" (cv.as? .i64)
    let vals ← fr.getMany args
    pure (declared, cv64.toNat, vals) : Res (Signature × Nat × List Val)) with
  | .ok (declared, addr, vals) =>
    match p.funcs.find? fun f => (mem.symbols f.name) == some addr with
    | some _ => none
    | none => externAtRaise env p mem declared addr vals
  | _ => none

/-- A `return_call fnN(args)` of frame `fr` calls an extern that unwinds (`stepReturnCall`). -/
def returnCallRaise (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) : Option (Exn × Mem) :=
  match (do
    let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
    let vals ← fr.getMany args
    checkTys s!"arguments of return_call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
    Res.check (AbiParam.tys ext.sig.returns == AbiParam.tys fr.func.sig.returns)
      s!"return_call to %{ext.name}: return types differ from the caller's"
    pure (ext, vals) : Res (ExtFunc × List Val)) with
  | .ok (ext, vals) =>
    match p.func? ext.name with
    | some _ => none
    | none =>
      match env.extern ext.name with
      | some g => match g vals mem with
        | .unwound e m => some (e, m)
        | _ => none
      | none => none
  | _ => none

/-- A `try_call fnN(args), et` of frame `fr` calls an extern that unwinds (`stepTryCall`). -/
def tryCallRaise (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) (et : ExnTable) : Option (Exn × Mem) :=
  match (do
    let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
    let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (fr.func.sigDecls.lookup et.sig)
    Res.check (AbiParam.tys sig.params == AbiParam.tys ext.sig.params &&
        AbiParam.tys sig.returns == AbiParam.tys ext.sig.returns)
      s!"try_call: sig{et.sig} is not the signature of fn{fn}"
    let base := fr.func.freshValue
    let bc ← tryNormal et base
    pure (ext.sig.returns.length, base, bc) : Res (Nat × ValueId × BlockCall)) with
  | .ok _ => callRaise env p mem fr fn args
  | _ => none

/-- A `try_call_indirect callee(args), et` of frame `fr` calls an extern that unwinds
(`stepTryCallIndirect`). -/
def tryCallIndRaise (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (callee : ValueId)
    (args : List ValueId) (et : ExnTable) : Option (Exn × Mem) :=
  match (do
    let sig ← Res.ofOption s!"unknown signature sig{et.sig}" (fr.func.sigDecls.lookup et.sig)
    let base := fr.func.freshValue
    let bc ← tryNormal et base
    pure (sig.returns.length, base, bc) : Res (Nat × ValueId × BlockCall)) with
  | .ok _ => callIndRaise env p mem fr et.sig callee args
  | _ => none

/-- The exception the current step raises, if its call reaches an extern that unwinds, with
the extern's memory. -/
def raiseAt? (env : XEnv) (p : Program) (s : State) : Option (Exn × Mem) :=
  match s.frame.body with
  | st :: _ =>
    match st.inst with
    | .call fn args => callRaise env p s.mem s.frame fn args
    | .callIndirect sig callee args => callIndRaise env p s.mem s.frame sig callee args
    | _ => none
  | [] =>
    match s.frame.term with
    | .returnCall fn args => returnCallRaise env p s.mem s.frame fn args
    | .tryCall fn args et => tryCallRaise env p s.mem s.frame fn args et
    | .tryCallIndirect callee args et => tryCallIndRaise env p s.mem s.frame callee args et
    | _ => none

/-! ## Steps and runs -/

/-- A step of `Clif.step` on `xs.s`, with the pending tables kept aligned with the callers: a
pushed caller records its `try_call`'s table (`pendingOf`), a resumed one drops its own. -/
def liftStep (xs : XState) : StepResult → XStepResult
  | .next s' =>
    .next ⟨s', if s'.callers.length = xs.s.callers.length + 1 then pendingOf xs.s :: xs.tries
      else if s'.callers.length + 1 = xs.s.callers.length then xs.tries.tail else xs.tries⟩
  | .done vals mem => .done vals mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m

/-- One small step with unwinding. -/
def stepX (env : XEnv) (p : Program) (xs : XState) : XStepResult :=
  match raiseAt? env p xs.s with
  | some (e, mem) => raiseIn xs e mem
  | none => liftStep xs (step env.toEnv p xs.s)

/-- Iterate `stepX` at most `fuel` times. -/
def runLoopX (env : XEnv) (p : Program) : Nat → XState → XOutcome
  | 0, _ => .outOfFuel
  | fuel + 1, xs =>
    match stepX env p xs with
    | .next xs' => runLoopX env p fuel xs'
    | .done vals mem => .returned vals mem
    | .unwound e mem => .unwound e mem
    | .trapped c => .trapped c
    | .stuck m => .stuck m

/-- The state of `runX` for a state of `Clif.run` without suspended `try_call`s. -/
def State.toX (s : State) : XState := ⟨s, s.callers.map fun _ => none⟩

/-- Run `f` on `args` from memory `mem` for at most `fuel` steps (`runWith`). -/
def runWithX (env : XEnv) (p : Program) (f : String) (args : List Val) (mem : Mem)
    (fuel : Nat) : XOutcome :=
  match initState p f args mem with
  | .ok s => runLoopX env p fuel s.toX
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-- Run `f` on `args` from the program's initial memory (`run`). -/
def runX (env : XEnv) (p : Program) (f : String) (args : List Val) (fuel : Nat) : XOutcome :=
  match p.initMem with
  | .ok mem => runWithX env p f args mem fuel
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-! ## The old semantics is the restriction to non-unwinding runs -/

theorem stepCall_of_callRaise {env : XEnv} {p : Program} {s : State} {rest : List Stmt}
    {results : List ValueId} {fn : FnRef} {args : List ValueId} {e : Exn} {m : Mem}
    (h : callRaise env p s.mem s.frame fn args = some (e, m)) :
    ∃ msg, stepCall env.toEnv p s rest results fn args = .stuck msg := by
  unfold callRaise at h
  unfold stepCall
  dsimp only
  split at h
  · rename_i ext vals heq
    rw [heq]
    simp only [StepResult.ofRes]
    split at h
    · simp at h
    · rename_i hp
      rw [hp]
      simp only [XEnv.toEnv]
      split at h
      · rename_i g hg
        rw [hg]
        simp only [Option.map]
        split at h
        · rename_i e' m' hgu
          rw [hgu]; exact ⟨_, rfl⟩
        · simp at h
      · simp at h
  · simp at h

theorem callExternAt_of_raise {env : XEnv} {p : Program} {mem : Mem} {declared : Signature}
    {addr : Nat} {vals : List Val} {e : Exn} {m : Mem}
    (h : externAtRaise env p mem declared addr vals = some (e, m)) :
    ∃ msg, callExternAt env.toEnv p mem declared addr vals = .stuck msg := by
  unfold externAtRaise at h
  unfold callExternAt
  split at h
  · rename_i name hn
    simp only [XEnv.toEnv] at hn ⊢
    rw [hn]
    simp only [Res.ofOption_some, Res.ok_bind]
    split at h
    · rename_i g hg
      rw [hg]
      simp only [Option.map, Res.ofOption_some, Res.ok_bind]
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        simp only [Res.check, hc.1, ite_true, Res.ok_bind, checkTys, hc.2]
        split at h
        · rename_i e' m' hgu
          rw [hgu]; exact ⟨_, rfl⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem stepCallIndirect_of_raise {env : XEnv} {p : Program} {s : State} {rest : List Stmt}
    {results : List ValueId} {sig : Nat} {callee : ValueId} {args : List ValueId} {e : Exn}
    {m : Mem} (h : callIndRaise env p s.mem s.frame sig callee args = some (e, m)) :
    ∃ msg, stepCallIndirect env.toEnv p s rest results sig callee args = .stuck msg := by
  unfold callIndRaise at h
  unfold stepCallIndirect
  dsimp only
  split at h
  · rename_i declared addr vals heq
    rw [heq]
    simp only [StepResult.ofRes]
    split at h
    · simp at h
    · rename_i hf
      rw [hf]
      obtain ⟨msg, hm⟩ := callExternAt_of_raise h
      rw [hm]
      exact ⟨msg, rfl⟩
  · simp at h

theorem stepReturnCall_of_raise {env : XEnv} {p : Program} {s : State} {fn : FnRef}
    {args : List ValueId} {e : Exn} {m : Mem}
    (h : returnCallRaise env p s.mem s.frame fn args = some (e, m)) :
    ∃ msg, stepReturnCall env.toEnv p s fn args = .stuck msg := by
  unfold returnCallRaise at h
  unfold stepReturnCall
  dsimp only
  split at h
  · rename_i ext vals heq
    rw [heq]
    simp only [StepResult.ofRes]
    split at h
    · simp at h
    · rename_i hp
      rw [hp]
      simp only [XEnv.toEnv]
      split at h
      · rename_i g hg
        rw [hg]
        simp only [Option.map]
        split at h
        · rename_i e' m' hgu
          rw [hgu]; exact ⟨_, rfl⟩
        · simp at h
      · simp at h
  · simp at h

theorem Frame.getMany_with (fr : Frame) (b : List Stmt) (t : Terminator) (xs : List ValueId) :
    Frame.getMany { fr with body := b, term := t } xs = fr.getMany xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [Frame.getMany, Frame.get, ih]

theorem callRaise_with (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (b : List Stmt)
    (t : Terminator) (fn : FnRef) (args : List ValueId) :
    callRaise env p mem { fr with body := b, term := t } fn args = callRaise env p mem fr fn args := by
  simp only [callRaise, Frame.getMany_with]

theorem callIndRaise_with (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (b : List Stmt)
    (t : Terminator) (sig : Nat) (callee : ValueId) (args : List ValueId) :
    callIndRaise env p mem { fr with body := b, term := t } sig callee args =
      callIndRaise env p mem fr sig callee args := by
  simp only [callIndRaise, Frame.getMany_with, Frame.get]

theorem stepTryCall_of_raise {env : XEnv} {p : Program} {s : State} {fn : FnRef}
    {args : List ValueId} {et : ExnTable} {e : Exn} {m : Mem}
    (h : tryCallRaise env p s.mem s.frame fn args et = some (e, m)) :
    ∃ msg, stepTryCall env.toEnv p s fn args et = .stuck msg := by
  unfold tryCallRaise at h
  unfold stepTryCall
  dsimp only
  split at h
  · rename_i x heq
    obtain ⟨n, base, bc⟩ := x
    rw [heq]
    simp only [StepResult.ofRes]
    exact stepCall_of_callRaise (s := { s with frame := { s.frame with body := [], term := .jump bc } })
      (by simpa only [callRaise_with] using h)
  · simp at h

theorem stepTryCallIndirect_of_raise {env : XEnv} {p : Program} {s : State} {callee : ValueId}
    {args : List ValueId} {et : ExnTable} {e : Exn} {m : Mem}
    (h : tryCallIndRaise env p s.mem s.frame callee args et = some (e, m)) :
    ∃ msg, stepTryCallIndirect env.toEnv p s callee args et = .stuck msg := by
  unfold tryCallIndRaise at h
  unfold stepTryCallIndirect
  dsimp only
  split at h
  · rename_i x heq
    obtain ⟨n, base, bc⟩ := x
    rw [heq]
    simp only [StepResult.ofRes]
    exact stepCallIndirect_of_raise
      (s := { s with frame := { s.frame with body := [], term := .jump bc } })
      (by simpa only [callIndRaise_with] using h)
  · simp at h

/-- A step that raises is `stuck` in `Clif.run`. -/
theorem step_of_raiseAt {env : XEnv} {p : Program} {s : State} {e : Exn} {m : Mem}
    (h : raiseAt? env p s = some (e, m)) : ∃ msg, step env.toEnv p s = .stuck msg := by
  unfold raiseAt? at h
  unfold step
  split at h
  · rename_i st rest hb
    rw [hb]
    simp only
    split at h
    · rename_i fn args hi
      rw [hi]; exact stepCall_of_callRaise h
    · rename_i sig callee args hi
      rw [hi]; exact stepCallIndirect_of_raise h
    · simp at h
  · rename_i hb
    rw [hb]
    simp only
    unfold stepTerm
    split at h
    · rename_i fn args ht
      rw [ht]; exact stepReturnCall_of_raise h
    · rename_i fn args et ht
      rw [ht]; exact stepTryCall_of_raise h
    · rename_i callee args et ht
      rw [ht]; exact stepTryCallIndirect_of_raise h
    · simp at h

/-- Where `Clif.step` is not `stuck`, `stepX` is that step. -/
theorem stepX_of_not_stuck {env : XEnv} {p : Program} {xs : XState}
    (h : ∀ msg, step env.toEnv p xs.s ≠ .stuck msg) :
    stepX env p xs = liftStep xs (step env.toEnv p xs.s) := by
  unfold stepX
  split
  · rename_i e m hr
    obtain ⟨msg, hm⟩ := step_of_raiseAt hr
    exact absurd hm (h msg)
  · rfl

/-- A run of `Clif.run`'s semantics that returns is a run of `runX`'s with the same result. -/
theorem runLoopX_of_returned {env : XEnv} {p : Program} :
    ∀ (fuel : Nat) (xs : XState) {vals : List Val} {mem : Mem},
      runLoop env.toEnv p fuel xs.s = .returned vals mem →
      runLoopX env p fuel xs = .returned vals mem
  | 0, xs, _, _, h => by simp at h
  | fuel + 1, xs, vals, mem, h => by
    rw [runLoop_succ] at h
    have hns : ∀ msg, step env.toEnv p xs.s ≠ .stuck msg := by
      intro msg hm; rw [hm] at h; simp at h
    unfold runLoopX
    rw [stepX_of_not_stuck hns]
    revert h
    cases step env.toEnv p xs.s with
    | next s' => intro h; exact runLoopX_of_returned fuel _ h
    | done v m => intro h; simpa [liftStep] using h
    | trapped c => intro h; simp at h
    | stuck m => intro h; simp at h

/-- A run of `Clif.run`'s semantics that traps is a run of `runX`'s with the same trap. -/
theorem runLoopX_of_trapped {env : XEnv} {p : Program} :
    ∀ (fuel : Nat) (xs : XState) {c : TrapCode},
      runLoop env.toEnv p fuel xs.s = .trapped c → runLoopX env p fuel xs = .trapped c
  | 0, xs, _, h => by simp at h
  | fuel + 1, xs, c, h => by
    rw [runLoop_succ] at h
    have hns : ∀ msg, step env.toEnv p xs.s ≠ .stuck msg := by
      intro msg hm; rw [hm] at h; simp at h
    unfold runLoopX
    rw [stepX_of_not_stuck hns]
    revert h
    cases step env.toEnv p xs.s with
    | next s' => intro h; exact runLoopX_of_trapped fuel _ h
    | done v m => intro h; simp at h
    | trapped c' => intro h; simpa [liftStep] using h
    | stuck m => intro h; simp at h

theorem Outcome.toX_ne_unwound (o : Outcome) (e : Exn) (m : Mem) : o.toX ≠ .unwound e m := by
  cases o <;> simp [Outcome.toX]

/-- No extern of `env` unwinds. -/
def XEnv.NoUnwind (env : XEnv) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals mem e m, g vals mem ≠ .unwound e m

theorem Env.toX_noUnwind (env : Env) : env.toX.NoUnwind := by
  intro n g hg vals mem e m
  simp only [Env.toX, Option.map_eq_some_iff] at hg
  obtain ⟨g0, _, rfl⟩ := hg
  exact Outcome.toX_ne_unwound _ e m

/-- No step raises in an environment whose externs never unwind. -/
theorem raiseAt_of_noUnwind {env : XEnv} (hN : env.NoUnwind) (p : Program) (s : State) :
    raiseAt? env p s = none := by
  unfold raiseAt?
  repeat' split
  all_goals first
    | rfl
    | (simp only [callRaise, callIndRaise, externAtRaise, returnCallRaise, tryCallRaise,
        tryCallIndRaise]
       repeat' split
       all_goals first | rfl | (exfalso; exact hN _ _ (by assumption) _ _ _ _ (by assumption)))

/-- For an environment of `Clif.run`, `runX` is `Clif.run`. -/
theorem runLoopX_toX (env : Env) (p : Program) :
    ∀ (fuel : Nat) (xs : XState), runLoopX env.toX p fuel xs = (runLoop env p fuel xs.s).toX
  | 0, _ => rfl
  | fuel + 1, xs => by
    unfold runLoopX
    simp only [stepX, raiseAt_of_noUnwind (Env.toX_noUnwind env), Env.toX_toEnv, runLoop_succ]
    cases step env p xs.s with
    | next s' => exact runLoopX_toX env p fuel _
    | done v m => rfl
    | trapped c => rfl
    | stuck m => rfl


/-! ## Non-vacuity

`%main(v0)`: `try_call %mid(v0), sig0, block1(ret0), [ tag3: block3(exn0), tag7: block2(exn0) ]`,
handlers returning `exn0` and `exn0 + 100`; `%mid(v0)`: `v1 = call %throw(v0); return v1`;
the extern `%throw` unwinds with the tag of its environment and payload `[v0]`. With tag 7 the
exception propagates out of `%mid` (a plain call) into `%main`, skips the `tag3` handler and is
caught by `tag7`; with tag 9 nothing catches it and the run ends `unwound`. -/

namespace UnwindWitness

def i64p : AbiParam := { ty := .i64 }
def sig1 : Signature := { params := [i64p], returns := [i64p] }

def mainTable : ExnTable where
  sig := 0
  normal := ⟨1, [.ret 0]⟩
  items := [.tag 3 ⟨3, [.exn 0]⟩, .tag 7 ⟨2, [.exn 0]⟩]

def mainFn : Function where
  name := "main"
  sig := sig1
  externs := [(0, { name := "mid", sig := sig1 })]
  sigDecls := [(0, sig1)]
  blocks := [
    { id := 0, params := [(0, .i64)],
      term := .tryCall 0 [0] mainTable },
    { id := 1, params := [(1, .i64)], term := .ret [1] },
    { id := 2, params := [(2, .i64)],
      body := [{ results := [3], inst := .iconst .i64 100 },
               { results := [4], inst := .binary .iadd .i64 2 3 }],
      term := .ret [4] },
    { id := 3, params := [(5, .i64)], term := .ret [5] }]

def midFn : Function where
  name := "mid"
  sig := sig1
  externs := [(0, { name := "throw", sig := sig1 })]
  blocks := [{ id := 0, params := [(0, .i64)],
               body := [{ results := [1], inst := .call 0 [0] }],
               term := .ret [1] }]

def prog : Program := { funcs := [mainFn, midFn] }

/-- `%throw` unwinds with tag `tag` and its argument as payload. -/
def throwSem (tag : Nat) (vals : List Val) (mem : Mem) : XOutcome :=
  .unwound ⟨fun t => t == tag, vals⟩ mem

def env (tag : Nat) : XEnv where
  extern n := if n = "throw" then some (throwSem tag) else none

/-- Caught by the `tag7` handler of the caller of the frame that called the thrower. -/
theorem caught : (runX (env 7) prog "main" [⟨.i64, 5⟩] 20).returnedVals? = some [⟨.i64, 105⟩] := by
  decide +kernel

/-- Not caught: the run ends `unwound` with the payload. -/
theorem uncaught : (runX (env 9) prog "main" [⟨.i64, 5⟩] 20).unwoundPayload? = some [⟨.i64, 5⟩] := by
  decide +kernel

/-- `Clif.run` gets stuck where the callee unwinds. -/
theorem old_stuck :
    (match run (env 7).toEnv prog "main" [⟨.i64, 5⟩] 20 with | .stuck _ => true | _ => false) =
      true := by
  decide +kernel

end UnwindWitness

end Clif
