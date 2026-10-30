import FV.Front.RenameStep
import FV.Clif.Unwind

/-!
# Renaming commutes with the CLIF semantics with unwinding (S10f)

`Clif.runLoopX_ren`, the counterpart of `FV/Front/RenameRun.lean`'s `runLoop_ren` for the runs
with unwinding (`Clif.runLoopX`, `FV/Clif/Unwind.lean`): running the renamed program in the
renamed environment with unwinding (`XEnv.ren σ`: an extern at a renamed name is the original
one on the memory with the original names) from the renamed state has the original run's
outcome, its memory renamed (`XOutcome.ren`), up to the messages of `stuck` (`XOutcome.erase`).
Exceptions carry no names (handler tags and payload values), so they are unchanged.
-/

namespace Clif

/-! ## Renaming the objects of the runs with unwinding -/

/-- Rename the memory of an outcome with unwinding. -/
def XOutcome.ren (σ : Ren) : XOutcome → XOutcome
  | .returned vals m => .returned vals (m.ren σ)
  | .unwound e m => .unwound e (m.ren σ)
  | o => o

/-- Forget the message of `stuck`. -/
def XOutcome.erase : XOutcome → XOutcome
  | .stuck _ => .stuck ""
  | o => o

/-- **The environment with unwinding of the renamed program** (`Env.ren`'s counterpart). -/
def XEnv.ren (σ : Ren) (E : XEnv) : XEnv where
  extern n := (E.extern (σ.bwd n)).map fun h vals m => (h vals (m.ren σ.symm)).ren σ
  names := E.names.map σ.fwd
  sigOf n := E.sigOf (σ.bwd n)

/-- Rename a state with unwinding (the pending tables have no names). -/
def XState.ren (σ : Ren) (xs : XState) : XState := ⟨xs.s.ren σ, xs.tries⟩

/-- Rename the state or memory of a step result with unwinding. -/
def XStepResult.ren (σ : Ren) : XStepResult → XStepResult
  | .next xs => .next (xs.ren σ)
  | .done vals m => .done vals (m.ren σ)
  | .unwound e m => .unwound e (m.ren σ)
  | r => r

/-- Forget the message of `stuck`. -/
def XStepResult.erase : XStepResult → XStepResult
  | .stuck _ => .stuck ""
  | r => r

theorem XOutcome.toOutcome_ren (σ : Ren) (o : XOutcome) :
    (o.ren σ).toOutcome = o.toOutcome.ren σ := by
  cases o <;> rfl

/-- The renamed environment with unwinding forgets unwinding as `Env.ren`. -/
theorem XEnv.ren_toEnv (σ : Ren) (E : XEnv) : (E.ren σ).toEnv = E.toEnv.ren σ := by
  simp only [XEnv.toEnv, XEnv.ren, Env.ren, Env.mk.injEq, and_true]
  funext n
  cases E.extern (σ.bwd n) <;> simp [XOutcome.toOutcome_ren]

@[simp] theorem XState.ren_s (σ : Ren) (xs : XState) : (xs.ren σ).s = xs.s.ren σ := rfl
@[simp] theorem XState.ren_tries (σ : Ren) (xs : XState) : (xs.ren σ).tries = xs.tries := rfl

theorem State.toX_ren (σ : Ren) (s : State) : (s.ren σ).toX = s.toX.ren σ := by
  simp [State.toX, XState.ren, List.map_map, Function.comp_def]

/-! ## Raising -/

theorem extern_ren (σ : Ren) (E : XEnv) (name : String) :
    (E.ren σ).extern (σ.fwd name) =
      (E.extern name).map fun h vals m => (h vals (m.ren σ.symm)).ren σ := by
  simp [XEnv.ren, σ.bwd_fwd]

theorem unwoundOf_ren (σ : Ren) (o : XOutcome) :
    (match o.ren σ with | .unwound e m => some (e, m) | _ => none) =
      (match o with | .unwound e m => some (e, m) | _ => none).map
        fun x : Exn × Mem => (x.1, x.2.ren σ) := by
  cases o <;> rfl

/-- The extern `name` called on `vals` unwinds (`callRaise`'s last part). -/
theorem externRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (name : String)
    (vals : List Val) :
    (match (p.rename σ.fwd).func? (σ.fwd name) with
      | some _ => none
      | none => match (E.ren σ).extern (σ.fwd name) with
        | some g => match g vals (m.ren σ) with
          | .unwound e m => some (e, m)
          | _ => none
        | none => none) =
    (match p.func? name with
      | some _ => none
      | none => match E.extern name with
        | some g => match g vals m with
          | .unwound e m => some (e, m)
          | _ => none
        | none => none).map fun x : Exn × Mem => (x.1, x.2.ren σ) := by
  rw [Program.rename_func?]
  cases p.func? name with
  | some _ => rfl
  | none =>
    simp only [Option.map_none, extern_ren]
    cases E.extern name with
    | none => rfl
    | some g =>
      simp only [Option.map_some, Mem.ren_ren_symm]
      exact unwoundOf_ren σ (g vals m)

theorem callRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) :
    callRaise (E.ren σ) (p.rename σ.fwd) (m.ren σ) (fr.ren σ) fn args =
      (callRaise E p m fr fn args).map fun x => (x.1, x.2.ren σ) := by
  unfold callRaise
  simp only [Frame.ren_func, Function.rename_extern?, Frame.ren_getMany]
  cases fr.func.extern? fn with
  | none => rfl
  | some ext =>
    simp only [Option.map_some, Res.ofOption, Res.ok_bind, ExtFunc.rename_name,
      ExtFunc.rename_sig]
    cases fr.getMany args with
    | trap c => rfl
    | stuck _ => rfl
    | ok vals =>
      simp only [Res.ok_bind, checkTys, Res.check]
      cases (vals.map (·.ty) == AbiParam.tys ext.sig.params) with
      | false => rfl
      | true =>
        simp only [↓reduceIte, Res.ok_bind, Res.pure_eq]
        exact externRaise_ren σ E p m ext.name vals

theorem externAtRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (declared : Signature)
    (addr : Nat) (vals : List Val) :
    externAtRaise (E.ren σ) (p.rename σ.fwd) (m.ren σ) declared addr vals =
      (externAtRaise E p m declared addr vals).map fun x => (x.1, x.2.ren σ) := by
  unfold externAtRaise
  have hfind : ((E.ren σ).names ++ (p.rename σ.fwd).externNames).find?
      (fun n => (m.ren σ).symbols n == some addr) =
      ((E.names ++ p.externNames).find? fun n => m.symbols n == some addr).map σ.fwd := by
    simp [XEnv.ren, Program.rename_externNames, ← List.map_append, List.find?_map,
      Function.comp_def, σ.bwd_fwd]
  rw [hfind]
  cases (E.names ++ p.externNames).find? fun n => m.symbols n == some addr with
  | none => rfl
  | some name =>
    simp only [Option.map_some, extern_ren]
    cases E.extern name with
    | none => rfl
    | some g =>
      have hs : (E.ren σ).sigOf (σ.fwd name) = E.sigOf name := by simp [XEnv.ren, σ.bwd_fwd]
      simp only [Option.map_some, Mem.ren_ren_symm, hs]
      split
      · exact unwoundOf_ren σ (g vals m)
      · rfl

theorem callIndRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (fr : Frame) (sig : Nat)
    (callee : ValueId) (args : List ValueId) :
    callIndRaise (E.ren σ) (p.rename σ.fwd) (m.ren σ) (fr.ren σ) sig callee args =
      (callIndRaise E p m fr sig callee args).map fun x => (x.1, x.2.ren σ) := by
  unfold callIndRaise
  simp only [Frame.ren_func, Function.rename_sigDecls, Frame.ren_get, Frame.ren_getMany]
  cases fr.func.sigDecls.lookup sig with
  | none => rfl
  | some declared =>
    simp only [Res.ofOption, Res.ok_bind]
    cases fr.get callee with
    | trap c => rfl
    | stuck _ => rfl
    | ok cv =>
      simp only [Res.ok_bind]
      cases cv.as? .i64 with
      | none => rfl
      | some cv64 =>
        simp only [Res.ok_bind]
        cases fr.getMany args with
        | trap c => rfl
        | stuck _ => rfl
        | ok vals =>
          simp only [Res.ok_bind, Res.pure_eq, Program.rename_find?_symbols]
          cases p.funcs.find? (fun f => m.symbols f.name == some cv64.toNat) with
          | some _ => rfl
          | none => exact externAtRaise_ren ..

theorem returnCallRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (fr : Frame)
    (fn : FnRef) (args : List ValueId) :
    returnCallRaise (E.ren σ) (p.rename σ.fwd) (m.ren σ) (fr.ren σ) fn args =
      (returnCallRaise E p m fr fn args).map fun x => (x.1, x.2.ren σ) := by
  unfold returnCallRaise
  simp only [Frame.ren_func, Function.rename_extern?, Frame.ren_getMany, Function.rename_sig]
  cases fr.func.extern? fn with
  | none => rfl
  | some ext =>
    simp only [Option.map_some, Res.ofOption, Res.ok_bind, ExtFunc.rename_name,
      ExtFunc.rename_sig]
    cases fr.getMany args with
    | trap c => rfl
    | stuck _ => rfl
    | ok vals =>
      simp only [Res.ok_bind, checkTys, Res.check]
      cases (vals.map (·.ty) == AbiParam.tys ext.sig.params) with
      | false => rfl
      | true =>
        simp only [↓reduceIte, Res.ok_bind]
        cases (AbiParam.tys ext.sig.returns == AbiParam.tys fr.func.sig.returns) with
        | false => rfl
        | true =>
          simp only [↓reduceIte, Res.ok_bind, Res.pure_eq]
          exact externRaise_ren σ E p m ext.name vals

theorem tryCallRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) (et : ExnTable) :
    tryCallRaise (E.ren σ) (p.rename σ.fwd) (m.ren σ) (fr.ren σ) fn args et =
      (tryCallRaise E p m fr fn args et).map fun x => (x.1, x.2.ren σ) := by
  unfold tryCallRaise
  simp only [Frame.ren_func, Function.rename_extern?, Function.rename_sigDecls,
    Function.rename_freshValue]
  cases fr.func.extern? fn with
  | none => rfl
  | some ext =>
    simp only [Option.map_some, Res.ofOption, Res.ok_bind, ExtFunc.rename_sig]
    cases fr.func.sigDecls.lookup et.sig with
    | none => rfl
    | some sig =>
      simp only [Res.ok_bind, Res.check]
      cases (AbiParam.tys sig.params == AbiParam.tys ext.sig.params &&
          AbiParam.tys sig.returns == AbiParam.tys ext.sig.returns) with
      | false => rfl
      | true =>
        simp only [↓reduceIte, Res.ok_bind]
        cases tryNormal et fr.func.freshValue with
        | trap c => rfl
        | stuck _ => rfl
        | ok bc => exact callRaise_ren ..

theorem tryCallIndRaise_ren (σ : Ren) (E : XEnv) (p : Program) (m : Mem) (fr : Frame)
    (callee : ValueId) (args : List ValueId) (et : ExnTable) :
    tryCallIndRaise (E.ren σ) (p.rename σ.fwd) (m.ren σ) (fr.ren σ) callee args et =
      (tryCallIndRaise E p m fr callee args et).map fun x => (x.1, x.2.ren σ) := by
  unfold tryCallIndRaise
  simp only [Frame.ren_func, Function.rename_sigDecls, Function.rename_freshValue]
  cases fr.func.sigDecls.lookup et.sig with
  | none => rfl
  | some sig =>
    simp only [Res.ofOption, Res.ok_bind]
    cases tryNormal et fr.func.freshValue with
    | trap c => rfl
    | stuck _ => rfl
    | ok bc => exact callIndRaise_ren ..

/-- **Which steps raise does not depend on the names.** -/
theorem raiseAt?_ren (σ : Ren) (E : XEnv) (p : Program) (s : State) :
    raiseAt? (E.ren σ) (p.rename σ.fwd) (s.ren σ) =
      (raiseAt? E p s).map fun x => (x.1, x.2.ren σ) := by
  unfold raiseAt?
  simp only [State.ren_frame, Frame.ren_body, Frame.ren_term, State.ren_mem]
  split
  · split
    · exact callRaise_ren ..
    · exact callIndRaise_ren ..
    · rfl
  · split
    · exact returnCallRaise_ren ..
    · exact tryCallRaise_ren ..
    · exact tryCallIndRaise_ren ..
    · rfl

theorem pendingOf_ren (σ : Ren) (s : State) : pendingOf (s.ren σ) = pendingOf s := by
  unfold pendingOf
  simp only [State.ren_frame, Frame.ren_body, Frame.ren_term]

theorem catchIn_ren (σ : Ren) (fr : Frame) (et : ExnTable) (e : Exn) :
    catchIn (fr.ren σ) et e = (catchIn fr et e).map fun r => Frame.ren σ <$> r := by
  unfold catchIn
  cases et.catch? e with
  | none => rfl
  | some d =>
    simp only [Option.map_some, Frame.ren_func, Function.rename_freshValue, Frame.ren_regs,
      Option.some.injEq]
    cases tryHandler d fr.func.freshValue with
    | ok bc =>
      simp only [Res.ok_bind]
      cases fr.regs.setMany ((List.range e.payload.length).map (fr.func.freshValue + ·))
        e.payload <;> rfl
    | trap c => rfl
    | stuck m => rfl

theorem ofRes_frame_ren (σ : Ren) (r : Res Frame) (k : Frame → XStepResult)
    (k' : Frame → XStepResult) (hk : ∀ fr, k' (fr.ren σ) = (k fr).ren σ) :
    XStepResult.ofRes (Frame.ren σ <$> r) k' = (XStepResult.ofRes r k).ren σ := by
  cases r <;> simp [XStepResult.ofRes, hk] <;> rfl

theorem unwindFrom_ren (σ : Ren) (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (m : Mem),
      unwindFrom e (fr.ren σ) (cs.map fun c => (c.1.ren σ, c.2)) ts (m.ren σ) =
        (unwindFrom e fr cs ts m).ren σ
  | fr, [], ts, m => by simp [unwindFrom, XStepResult.ren]
  | fr, (c, v) :: cs, [], m => by simp [unwindFrom, XStepResult.ren]
  | fr, (c, v) :: cs, t :: ts, m => by
    simp only [List.map_cons, unwindFrom, Frame.ren_slots, Mem.ren_free, Mem.ren_leave]
    cases t with
    | none => exact unwindFrom_ren σ e c cs ts _
    | some et =>
      simp only [Option.bind_some, catchIn_ren]
      cases catchIn c et e with
      | none => exact unwindFrom_ren σ e c cs ts _
      | some r =>
        simp only [Option.map_some]
        exact ofRes_frame_ren σ r _ _ fun _ => rfl

theorem raiseIn_ren (σ : Ren) (xs : XState) (e : Exn) (m : Mem) :
    raiseIn (xs.ren σ) e (m.ren σ) = (raiseIn xs e m).ren σ := by
  unfold raiseIn
  simp only [XState.ren_s, pendingOf_ren, State.ren_frame]
  cases pendingOf xs.s with
  | none => exact unwindFrom_ren σ e _ _ _ _
  | some et =>
    simp only [Option.bind_some, catchIn_ren]
    cases catchIn xs.s.frame et e with
    | none => exact unwindFrom_ren σ e _ _ _ _
    | some r =>
      simp only [Option.map_some]
      exact ofRes_frame_ren σ r _ _ fun _ => rfl

/-! ## Steps and runs -/

theorem liftStep_ren (σ : Ren) (xs : XState) {r r' : StepResult}
    (h : r'.erase = (r.ren σ).erase) :
    (liftStep (xs.ren σ) r').erase = ((liftStep xs r).ren σ).erase := by
  cases r <;> cases r' <;>
    simp_all [StepResult.erase, StepResult.ren, liftStep, XStepResult.erase, XStepResult.ren,
      XState.ren, pendingOf_ren]

/-- **Renaming commutes with a step with unwinding**, up to the messages of `stuck`. -/
theorem stepX_ren (σ : Ren) (E : XEnv) (p : Program) (xs : XState) :
    (stepX (E.ren σ) (p.rename σ.fwd) (xs.ren σ)).erase = ((stepX E p xs).ren σ).erase := by
  unfold stepX
  rw [XState.ren_s, raiseAt?_ren]
  cases raiseAt? E p xs.s with
  | some x =>
    obtain ⟨e, m⟩ := x
    simp only [Option.map_some, raiseIn_ren]
  | none =>
    simp only [Option.map_none]
    apply liftStep_ren
    rw [XEnv.ren_toEnv]
    exact step_ren σ E.toEnv p xs.s

/-- **Renaming commutes with the runs with unwinding**: the renamed program in the renamed
environment from the renamed state has the original outcome, its memory renamed, up to the
messages of `stuck`. -/
theorem runLoopX_ren (σ : Ren) (E : XEnv) (p : Program) (n : Nat) (xs : XState) :
    (runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ)).erase =
      ((runLoopX E p n xs).ren σ).erase := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    have h := stepX_ren σ E p xs
    simp only [runLoopX]
    cases hs : stepX E p xs <;> cases hr : stepX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) <;>
      simp only [hs, hr, XStepResult.erase, XStepResult.ren, XStepResult.next.injEq,
        XStepResult.done.injEq, XStepResult.unwound.injEq, XStepResult.trapped.injEq,
        reduceCtorEq] at h ⊢
    all_goals first
      | (subst h; exact ih _)
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | (subst h; rfl)
      | rfl

/-- An exception leaving the original run leaves the renamed one, its memory renamed. -/
theorem runLoopX_ren_unwound (σ : Ren) (E : XEnv) (p : Program) (n : Nat) (xs : XState)
    {e : Exn} {m : Mem} (h : runLoopX E p n xs = .unwound e m) :
    runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ) = .unwound e (m.ren σ) := by
  have hr := runLoopX_ren σ E p n xs
  rw [h] at hr
  revert hr
  cases runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ) <;>
    simp [XOutcome.erase, XOutcome.ren]

/-- A return of the original run is a return of the renamed one. -/
theorem runLoopX_ren_returned (σ : Ren) (E : XEnv) (p : Program) (n : Nat) (xs : XState)
    {vals : List Val} {m : Mem} (h : runLoopX E p n xs = .returned vals m) :
    runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ) = .returned vals (m.ren σ) := by
  have hr := runLoopX_ren σ E p n xs
  rw [h] at hr
  revert hr
  cases runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ) <;>
    simp [XOutcome.erase, XOutcome.ren]

/-- A trap of the original run is a trap of the renamed one. -/
theorem runLoopX_ren_trapped (σ : Ren) (E : XEnv) (p : Program) (n : Nat) (xs : XState)
    {c : TrapCode} (h : runLoopX E p n xs = .trapped c) :
    runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ) = .trapped c := by
  have hr := runLoopX_ren σ E p n xs
  rw [h] at hr
  revert hr
  cases runLoopX (E.ren σ) (p.rename σ.fwd) n (xs.ren σ) <;>
    simp [XOutcome.erase, XOutcome.ren]

end Clif
