import FV.Clif.Unwind
import FV.Opt.Proof.SemSim

/-!
# Raising steps by their preludes (S10f, #233)

Facts about `Clif.stepX` (`FV/Clif/Unwind.lean`) in the terms of the frame simulations of
`FV/Opt/Proof/SemSim.lean`: a `call` raises exactly when its prelude (`callArgs`) gives an
extern that unwinds on those arguments (`extRaise`), a `return_call` likewise (`tailArgs`); the
handler a `try_call`'s table resumes (`Clif.catchIn`) reads only the frame's function and
registers; leaving frames keeps the symbols; `liftStep` as a function of the call depth, the
pending table and the tables of the callers (`liftWith`).
-/

namespace Opt

open Clif

/-! ## Externs -/

/-- The extern `ext` called on `vals` from memory `mem` unwinds (`Clif.callRaise` after its
prelude). -/
def extRaise (env : XEnv) (p : Program) (mem : Mem) (ext : ExtFunc) (vals : List Val) :
    Option (Exn × Mem) :=
  match p.func? ext.name with
  | some _ => none
  | none =>
    match env.extern ext.name with
    | some g => match g vals mem with
      | .unwound e m => some (e, m)
      | _ => none
    | none => none

theorem callRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) :
    callRaise env p mem fr fn args = match callArgs fr fn args with
      | .ok (ext, vals) => extRaise env p mem ext vals
      | _ => none := by
  unfold callRaise
  cases h : callArgs fr fn args with
  | ok x =>
    obtain ⟨ext, vals⟩ := x
    unfold callArgs at h
    rw [h]
    rfl
  | trap c =>
    unfold callArgs at h
    rw [h]
  | stuck m =>
    unfold callArgs at h
    rw [h]

theorem returnCallRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) :
    returnCallRaise env p mem fr fn args = match tailArgs fr fn args with
      | .ok (ext, vals) => extRaise env p mem ext vals
      | _ => none := by
  unfold returnCallRaise
  cases h : tailArgs fr fn args with
  | ok x =>
    obtain ⟨ext, vals⟩ := x
    unfold tailArgs at h
    rw [h]
    rfl
  | trap c =>
    unfold tailArgs at h
    rw [h]
  | stuck m =>
    unfold tailArgs at h
    rw [h]

theorem callRaise_inv {env : XEnv} {p : Program} {mem : Mem} {fr : Frame} {fn : FnRef}
    {args : List ValueId} {r : Exn × Mem} (h : callRaise env p mem fr fn args = some r) :
    ∃ ext vals, callArgs fr fn args = .ok (ext, vals) ∧ extRaise env p mem ext vals = some r := by
  rw [callRaise_eq] at h
  split at h
  · rename_i ext vals hc
    exact ⟨ext, vals, hc, h⟩
  · cases h

theorem returnCallRaise_inv {env : XEnv} {p : Program} {mem : Mem} {fr : Frame} {fn : FnRef}
    {args : List ValueId} {r : Exn × Mem} (h : returnCallRaise env p mem fr fn args = some r) :
    ∃ ext vals, tailArgs fr fn args = .ok (ext, vals) ∧ extRaise env p mem ext vals = some r := by
  rw [returnCallRaise_eq] at h
  split at h
  · rename_i ext vals hc
    exact ⟨ext, vals, hc, h⟩
  · cases h

/-- Externs keep the link-time symbols, when they return and when they unwind. -/
def EnvKeepsSymbolsX (env : XEnv) : Prop :=
  ∀ name g, env.extern name = some g → ∀ vals m,
    (∀ rvals m', g vals m = .returned rvals m' → m'.symbols = m.symbols) ∧
    (∀ e m', g vals m = .unwound e m' → m'.symbols = m.symbols)

theorem EnvKeepsSymbolsX.toEnv {env : XEnv} (h : EnvKeepsSymbolsX env) :
    EnvKeepsSymbols env.toEnv := by
  intro name f hf vals m rvals m' hr
  simp only [XEnv.toEnv, Option.map_eq_some_iff] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  have hr' : (g vals m).toOutcome = .returned rvals m' := hr
  refine (h name g hg vals m).1 rvals m' ?_
  cases hgo : g vals m with
  | returned v mm =>
    rw [hgo] at hr'
    simp only [XOutcome.toOutcome, Outcome.returned.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    rfl
  | unwound e mm => rw [hgo] at hr'; simp [XOutcome.toOutcome] at hr'
  | trapped c => rw [hgo] at hr'; simp [XOutcome.toOutcome] at hr'
  | stuck msg => rw [hgo] at hr'; simp [XOutcome.toOutcome] at hr'
  | outOfFuel => rw [hgo] at hr'; simp [XOutcome.toOutcome] at hr'

theorem extRaise_symbols {env : XEnv} {p : Program} {mem : Mem} {ext : ExtFunc}
    {vals : List Val} {e : Exn} {m : Mem} (hE : EnvKeepsSymbolsX env)
    (h : extRaise env p mem ext vals = some (e, m)) : m.symbols = mem.symbols := by
  unfold extRaise at h
  split at h
  · cases h
  · split at h
    · rename_i g hg
      split at h
      · rename_i e' m' hgo
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (hE _ g hg vals mem).2 _ _ hgo
      · cases h
    · cases h

theorem externAtRaise_symbols {env : XEnv} {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} {e : Exn} {m : Mem} (hE : EnvKeepsSymbolsX env)
    (h : externAtRaise env p mem d a vals = some (e, m)) : m.symbols = mem.symbols := by
  unfold externAtRaise at h
  split at h
  · split at h
    · rename_i g hg
      split at h
      · split at h
        · rename_i e' m' hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (hE _ g hg vals mem).2 _ _ hgo
        · cases h
      · cases h
    · cases h
  · cases h

/-- Leaving a frame keeps the symbols. -/
theorem leave_free_symbols (m : Mem) (bases : List Nat) :
    ((m.free bases).leave).symbols = m.symbols := by
  rw [Mem.leave_symbols]; rfl

/-! ## Handlers -/

theorem catchIn_bt (fr : Frame) (b : List Stmt) (t : Terminator) (et : ExnTable) (e : Exn) :
    catchIn { fr with body := b, term := t } et e = catchIn fr et e := rfl

theorem catchIn_eq_none {fr : Frame} {et : ExnTable} {e : Exn} :
    catchIn fr et e = none ↔ et.catch? e = none := by
  unfold catchIn
  cases et.catch? e <;> simp

theorem catchIn_ok {fr : Frame} {et : ExnTable} {e : Exn} {fr1 : Frame}
    (h : catchIn fr et e = some (.ok fr1)) :
    ∃ d bc regs, et.catch? e = some d ∧ tryHandler d fr.func.freshValue = .ok bc ∧
      fr.regs.setMany ((List.range e.payload.length).map (fr.func.freshValue + ·)) e.payload =
        some regs ∧
      fr1 = { fr with regs, body := [], term := .jump bc } := by
  unfold catchIn at h
  cases hc : et.catch? e with
  | none => rw [hc] at h; cases h
  | some d =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨bc, hbc, regs, hr, rfl⟩ := h
    exact ⟨d, bc, regs, rfl, hbc, hr, rfl⟩

theorem catchIn_of {fr : Frame} {et : ExnTable} {e : Exn} {d : TryDest} {bc : BlockCall}
    {regs : Regs} (hd : et.catch? e = some d) (hb : tryHandler d fr.func.freshValue = .ok bc)
    (hr : fr.regs.setMany ((List.range e.payload.length).map (fr.func.freshValue + ·)) e.payload =
      some regs) :
    catchIn fr et e = some (.ok { fr with regs, body := [], term := .jump bc }) := by
  unfold catchIn
  rw [hd]
  simp only [Option.map_some, hb, hr, Res.ofOption, bind, Res.bind, pure]

theorem tryHandler_ne_trap (d : TryDest) (base : ValueId) (c : TrapCode) :
    tryHandler d base ≠ .trap c := by
  unfold tryHandler
  generalize d.args = l
  have : ∀ l : List TryArg, (l.mapM fun
      | .val v => (pure v : Res ValueId)
      | .exn i => pure (base + i)
      | .ret _ => .stuck "try_call: return value on an exception edge") ≠ .trap c := by
    intro l
    induction l with
    | nil => simp [pure]
    | cons a l ih =>
      simp only [List.mapM_cons, ne_eq, Res.bind_eq_trap, not_or, not_exists, not_and]
      refine ⟨by cases a <;> simp [pure], fun b _ => ⟨ih, fun bs _ => by simp [pure]⟩⟩
  simp only [ne_eq, Res.bind_eq_trap, not_or, not_exists, not_and]
  exact ⟨this l, fun _ _ => by simp [pure]⟩

theorem catchIn_ne_trap (fr : Frame) (et : ExnTable) (e : Exn) (c : TrapCode) :
    catchIn fr et e ≠ some (.trap c) := by
  unfold catchIn
  cases et.catch? e with
  | none => simp
  | some d =>
    simp only [Option.map_some, ne_eq, Option.some.injEq, Res.bind_eq_trap, not_or, not_exists,
      not_and]
    refine ⟨tryHandler_ne_trap d _ c, fun _ _ => ?_⟩
    cases fr.regs.setMany _ _ <;> simp [Res.ofOption, pure]

theorem catchIn_func {fr : Frame} {et : ExnTable} {e : Exn} {fr1 : Frame}
    (h : catchIn fr et e = some (.ok fr1)) :
    fr1.func = fr.func ∧ fr1.slots = fr.slots ∧ fr1.body = [] ∧ ∃ bc, fr1.term = .jump bc := by
  obtain ⟨d, bc, regs, -, -, -, rfl⟩ := catchIn_ok h
  exact ⟨rfl, rfl, rfl, bc, rfl⟩

theorem bind_catchIn {c : Frame} {t : Option ExnTable} {e : Exn} {r : Res Frame}
    (h : t.bind (catchIn c · e) = some r) : ∃ et, t = some et ∧ catchIn c et e = some r := by
  cases t with
  | none => cases h
  | some et => exact ⟨et, rfl, h⟩

/-! ## Handler successors -/

/-- The arguments of a handler successor, the payload from `b` (`Clif.tryHandler`). -/
def resolveH (b : ValueId) : List TryArg → Res (List ValueId)
  | [] => .ok []
  | a :: l => do
    let x ← (match a with
      | .val v => pure v
      | .exn i => pure (b + i)
      | .ret _ => .stuck "try_call: return value on an exception edge")
    let xs ← resolveH b l
    pure (x :: xs)

theorem tryHandler_eq (d : TryDest) (b : ValueId) :
    tryHandler d b = (do let args ← resolveH b d.args; pure { block := d.block, args }) := by
  unfold tryHandler
  congr 1
  generalize d.args = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, resolveH, ih]
    cases a <;> rfl

theorem tryHandler_block {d : TryDest} {b : ValueId} {bc : BlockCall}
    (h : tryHandler d b = .ok bc) : bc.block = d.block := by
  rw [tryHandler_eq] at h
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem catch?_mapVals (σ : ValueId → ValueId) (et : ExnTable) (e : Exn) :
    (et.mapVals σ).catch? e = (et.catch? e).map (·.mapVals σ) := by
  unfold ExnTable.catch? ExnTable.mapVals
  simp only
  generalize et.items = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | tag n d =>
      simp only [List.map_cons, List.findSome?_cons]
      cases e.catches n
      · simpa using ih
      · simp
    | default d => simp
    | context v =>
      simp only [List.map_cons, List.findSome?_cons]
      exact ih

theorem catch?_mem {et : ExnTable} {e : Exn} {d : TryDest} (h : et.catch? e = some d) :
    d ∈ et.handlers := by
  unfold ExnTable.catch? at h
  unfold ExnTable.handlers
  obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some h
  rw [List.mem_filterMap]
  refine ⟨a, ha, ?_⟩
  cases a with
  | tag n d' =>
    simp only at hfa ⊢
    split at hfa
    · exact hfa
    · cases hfa
  | default d' => simpa using hfa
  | context v => simp at hfa

theorem handler_vals {et : ExnTable} {d : TryDest} (hd : d ∈ et.handlers) {v : ValueId}
    (hv : v ∈ d.vals) : v ∈ et.vals := by
  unfold ExnTable.handlers at hd
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.1 hd
  unfold ExnTable.vals
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, ?_⟩)
  cases a with
  | tag n d' =>
    simp only [Option.some.injEq] at hfa
    subst hfa
    exact hv
  | default d' =>
    simp only [Option.some.injEq] at hfa
    subst hfa
    exact hv
  | context w => cases hfa

theorem handler_succ {et : ExnTable} {d : TryDest} (hd : d ∈ et.handlers) :
    d.block ∈ et.dests.map (·.block) :=
  List.mem_map.2 ⟨d, List.mem_append_left _ hd, rfl⟩

/-! ## Pending tables -/

theorem pendingOf_cons {s : State} {st : Stmt} {rest : List Stmt} (hb : s.frame.body = st :: rest) :
    pendingOf s = none := by
  simp [pendingOf, hb]

theorem pendingOf_try {s : State} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    (hb : s.frame.body = []) (ht : s.frame.term = .tryCall fn args et) : pendingOf s = some et := by
  simp [pendingOf, hb, ht]

theorem pendingOf_tryInd {s : State} {c : ValueId} {args : List ValueId} {et : ExnTable}
    (hb : s.frame.body = []) (ht : s.frame.term = .tryCallIndirect c args et) :
    pendingOf s = some et := by
  simp [pendingOf, hb, ht]

theorem pendingOf_notTry {s : State} (hb : s.frame.body = []) (ht : s.frame.term.isTry = false) :
    pendingOf s = none := by
  unfold pendingOf
  rw [hb]
  cases h : s.frame.term <;> rw [h] at ht <;> simp_all [Terminator.isTry]

/-! ## Which states raise -/

theorem raiseAt_jump {env : XEnv} {p : Program} {s : State} {bc : BlockCall}
    (hb : s.frame.body = []) (ht : s.frame.term = .jump bc) : raiseAt? env p s = none := by
  simp [raiseAt?, hb, ht]

theorem callIndRaise_symbols {env : XEnv} {p : Program} {mem : Mem} {fr : Frame} {sig : Nat}
    {callee : ValueId} {args : List ValueId} {e : Exn} {m : Mem} (hE : EnvKeepsSymbolsX env)
    (h : callIndRaise env p mem fr sig callee args = some (e, m)) : m.symbols = mem.symbols := by
  unfold callIndRaise at h
  split at h
  · split at h
    · cases h
    · exact externAtRaise_symbols hE h
  · cases h

/-- The memory an extern unwinds with has the symbols of the memory it was called in. -/
theorem raiseAt_symbols {env : XEnv} {p : Program} {s : State} {e : Exn} {m : Mem}
    (hE : EnvKeepsSymbolsX env) (h : raiseAt? env p s = some (e, m)) :
    m.symbols = s.mem.symbols := by
  unfold raiseAt? at h
  split at h
  · split at h
    · obtain ⟨ext, vals, -, hx⟩ := callRaise_inv h; exact extRaise_symbols hE hx
    · exact callIndRaise_symbols hE h
    · cases h
  · split at h
    · obtain ⟨ext, vals, -, hx⟩ := returnCallRaise_inv h; exact extRaise_symbols hE hx
    · unfold tryCallRaise at h
      split at h
      · obtain ⟨ext, vals, -, hx⟩ := callRaise_inv h; exact extRaise_symbols hE hx
      · cases h
    · unfold tryCallIndRaise at h
      split at h
      · exact callIndRaise_symbols hE h
      · cases h
    · cases h

/-! ## Lifted steps -/

/-- `Clif.liftStep` from the call depth `n`, the pending table `t` and the callers' tables. -/
def liftWith (n : Nat) (t : Option ExnTable) (ts : List (Option ExnTable)) : StepResult →
    XStepResult
  | .next s' => .next ⟨s', if s'.callers.length = n + 1 then t :: ts
      else if s'.callers.length + 1 = n then ts.tail else ts⟩
  | .done vals mem => .done vals mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m

theorem liftStep_eq (xs : XState) (r : StepResult) :
    liftStep xs r = liftWith xs.s.callers.length (pendingOf xs.s) xs.tries r := by
  cases r <;> rfl

theorem liftWith_same {n : Nat} {t : Option ExnTable} {ts : List (Option ExnTable)} {s' : State}
    (h : s'.callers.length = n) : liftWith n t ts (.next s') = .next ⟨s', ts⟩ := by
  simp [liftWith, h]

theorem liftWith_push {n : Nat} {t : Option ExnTable} {ts : List (Option ExnTable)} {s' : State}
    (h : s'.callers.length = n + 1) : liftWith n t ts (.next s') = .next ⟨s', t :: ts⟩ := by
  simp [liftWith, h]

theorem liftWith_pop {n : Nat} {t : Option ExnTable} {ts : List (Option ExnTable)} {s' : State}
    (h : s'.callers.length + 1 = n) : liftWith n t ts (.next s') = .next ⟨s', ts.tail⟩ := by
  subst h
  simp only [liftWith]
  split
  · omega
  · simp

theorem stepX_raise {env : XEnv} {p : Program} {xs : XState} {e : Exn} {m : Mem}
    (h : raiseAt? env p xs.s = some (e, m)) : stepX env p xs = raiseIn xs e m := by
  unfold stepX; rw [h]

theorem stepX_none {env : XEnv} {p : Program} {xs : XState} (h : raiseAt? env p xs.s = none) :
    stepX env p xs = liftStep xs (step env.toEnv p xs.s) := by
  unfold stepX; rw [h]

theorem runLoopX_of_next {env : XEnv} {p : Program} {xs xs' : XState}
    (h : stepX env p xs = .next xs') (n : Nat) : runLoopX env p (n + 1) xs = runLoopX env p n xs' := by
  rw [runLoopX, h]

/-- A `next` step that keeps the callers is a step with unwinding that keeps the tables. -/
theorem stepX_of_same {env : XEnv} {p : Program} {s s1 : State} (ts : List (Option ExnTable))
    (h : step env.toEnv p s = .next s1) (hc : s1.callers = s.callers) :
    stepX env p ⟨s, ts⟩ = .next ⟨s1, ts⟩ := by
  rw [stepX_of_not_stuck (xs := ⟨s, ts⟩) (fun msg hm => by
    have : step env.toEnv p s = .stuck msg := hm
    rw [h] at this; cases this), show (⟨s, ts⟩ : XState).s = s from rfl, h, liftStep_eq]
  exact liftWith_same (by rw [hc])

/-! ## Local steps -/

theorem lstep_tail_inv' {fr : Frame} {mem : Mem} {ext : ExtFunc} {vals : List Val}
    (h : lstep fr mem = .tail ext vals) :
    fr.body = [] ∧ ∃ fn args, fr.term = .returnCall fn args ∧ tailArgs fr fn args = .ok (ext, vals) := by
  have hb := lstep_tail_inv h
  refine ⟨hb, ?_⟩
  obtain ⟨func, regs, slots, body, term⟩ := fr
  simp only at hb
  subst hb
  cases term with
  | returnCall fn args =>
    refine ⟨fn, args, rfl, ?_⟩
    simp only [lstep] at h
    cases ht : tailArgs ⟨func, regs, slots, [], .returnCall fn args⟩ fn args with
    | ok x =>
      rw [ht] at h
      obtain ⟨e, v⟩ := x
      simp only [LRes.ofRes, LRes.tail.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | trap c => rw [ht] at h; cases h
    | stuck m => rw [ht] at h; cases h
  | _ =>
    simp only [lstep, LRes.ofRes] at h <;> (repeat' split at h) <;> cases h

end Opt
