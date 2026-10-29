module

public import FV.E2E.LinkClif
public import FV.Clif.Unwind

@[expose] public section

/-!
# Linking at the CLIF level with unwinding (S10f, #233)

`docs/plans/unwinding.md` §4. `runLoop_link` (`FV/E2E/LinkClif.lean`) for the runs with unwinding
`Clif.runLoopX`: a whole-program run (a call of a function of `P` enters it, an exception
propagates through the suspended frames of `P` by their pending tables `XState.tries`) is the
per-function run of `P.only f` under `linkEnvX P env`, in which a call of another function `g`
of `P` is atomic: its whole-program run with unwinding (`runLimX`), whose `unwound` outcome is
the extern's exceptional result — the caller then raises it at the call (`Clif.raiseIn`), as the
whole-program run's unwinding does when the exception leaves `g`'s bottom frame.

* `XState.below`, `stepX_below`, `runLoopX_below_*`: a run with more callers (and their pending
  tables) below the stack is the run without them until the bottom frame returns
  (`resumeStepX`) or is left by an exception (`resumeUnwind`).
* `runLimX`: the outcome with unbounded fuel.
* `XInv` (frames of `P`, one pending table per caller; `initState_xinv`), kept by `stepX`
  (`stepX_next_xinv`), with the bottom frame's function (`runLoopX_returned_tys`).
* `runLoopX_link`: **every complete whole-program run with unwinding (returned, trapped or
  unwound) is a complete per-function run** under `linkEnvX P env` (`LinkFree`, `IndFree`,
  distinct names, as `runLoop_link`). Non-vacuity: `UnwindLinkWitness.link_caught` (an
  exception leaving a callee of `P` caught by its caller's `try_call`).
-/

namespace Clif

/-! ## More callers below the stack -/

/-- `xs` with the callers `M` and their pending tables `T` below its stack. -/
def XState.below (xs : XState) (M : List (Frame × List ValueId)) (T : List (Option ExnTable)) :
    XState :=
  ⟨xs.s.below M, xs.tries ++ T⟩

/-- One pending table per caller. -/
def XState.Aligned (xs : XState) : Prop := xs.tries.length = xs.s.callers.length

/-- An exception that left the bottom frame (memory `mem`, the frame left) continues into the
callers `M` with the pending tables `T` (`unwindFrom` after its first frame). -/
def resumeUnwind (e : Exn) : List (Frame × List ValueId) → List (Option ExnTable) → Mem →
    XStepResult
  | [], _, mem => .unwound e mem
  | (c, _) :: cs, t :: ts, mem =>
    match t.bind (catchIn c · e) with
    | some r => XStepResult.ofRes r fun fr' => .next ⟨{ frame := fr', callers := cs, mem }, ts⟩
    | none => unwindFrom e c cs ts mem
  | _ :: _, [], _ => .stuck "unwinding: no pending table for a caller"

theorem unwindFrom_eq (e : Exn) (fr : Frame) (K : List (Frame × List ValueId))
    (T : List (Option ExnTable)) (mem : Mem) :
    unwindFrom e fr K T mem = resumeUnwind e K T ((mem.free (fr.slots.map (·.2))).leave) := by
  match K, T with
  | [], _ => rfl
  | (c, _) :: cs, t :: ts => rfl
  | _ :: _, [] => rfl

/-- A completed bottom activation returns to the callers `M` (their tables `T`). -/
def resumeStepX (M : List (Frame × List ValueId)) (T : List (Option ExnTable)) (vals : List Val)
    (mem : Mem) : XStepResult :=
  match resumeStep M vals mem with
  | .next s => .next ⟨s, T.tail⟩
  | .done v m => .done v m
  | .trapped c => .trapped c
  | .stuck m => .stuck m

/-- A step result with the callers `M` (tables `T`) below the stack. -/
def XStepResult.below (M : List (Frame × List ValueId)) (T : List (Option ExnTable)) :
    XStepResult → XStepResult
  | .next xs => .next (xs.below M T)
  | .done vals mem => resumeStepX M T vals mem
  | .unwound e mem => resumeUnwind e M T mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m

theorem XStepResult.ofRes_below {α : Type} (X : Res α) (k : α → XStepResult)
    (M : List (Frame × List ValueId)) (T : List (Option ExnTable)) :
    (XStepResult.ofRes X k).below M T = XStepResult.ofRes X fun a => (k a).below M T := by
  cases X <;> rfl

theorem unwindFrom_below (e : Exn) (M : List (Frame × List ValueId)) (T : List (Option ExnTable)) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem),
      ts.length = cs.length →
      unwindFrom e fr (cs ++ M) (ts ++ T) mem = (unwindFrom e fr cs ts mem).below M T
  | fr, [], [], mem, _ => by
    rw [List.nil_append, List.nil_append, unwindFrom_eq]
    rfl
  | fr, (c, rs) :: cs, t :: ts, mem, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.cons_append, unwindFrom]
    split
    · rw [XStepResult.ofRes_below]
      rfl
    · exact unwindFrom_below e M T c cs ts _ h
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h

theorem raiseAt?_below (env : XEnv) (p : Program) (s : State) (M : List (Frame × List ValueId)) :
    raiseAt? env p (s.below M) = raiseAt? env p s := rfl

theorem pendingOf_below (s : State) (M : List (Frame × List ValueId)) :
    pendingOf (s.below M) = pendingOf s := rfl

theorem raiseIn_below (xs : XState) (e : Exn) (mem : Mem) (M : List (Frame × List ValueId))
    (T : List (Option ExnTable)) (ha : xs.Aligned) :
    raiseIn (xs.below M T) e mem = (raiseIn xs e mem).below M T := by
  unfold raiseIn
  simp only [XState.below, pendingOf_below, State.below_frame, State.below_callers]
  split
  · rw [XStepResult.ofRes_below]
    rfl
  · exact unwindFrom_below e M T _ _ _ mem ha

/-! ## How a step changes the callers -/

/-- `b` is `a`, one caller pushed on `a`, or `a` with one caller popped. -/
def CallersStep (a b : List (Frame × List ValueId)) : Prop :=
  b = a ∨ (∃ c, b = c :: a) ∨ ∃ c, a = c :: b

/-- A step of a frame of a function of `P` (no `return_call`) pushes, pops or keeps a caller. -/
theorem step_callers {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    {s s1 : State} (hI : LFrame P s.frame) (h : step env p s = .next s1) :
    CallersStep s.callers s1.callers := by
  have hcall : ∀ (t : State) rest rs ext vals, t.callers = s.callers →
      Opt.callCont env p t rest rs ext vals = .next s1 → CallersStep s.callers s1.callers := by
    intro t rest rs ext vals htc hc
    rcases callCont_next hc with ⟨hc1, -⟩ | ⟨hc1, -⟩
    · exact .inr (.inl ⟨_, by rw [hc1, htc]⟩)
    · exact .inl (by rw [hc1, htc])
  have hind : ∀ (t : State) rest rs sig d a v, t.callers = s.callers →
      indCont env p t rest rs sig d a v = .next s1 → CallersStep s.callers s1.callers := by
    intro t rest rs sig d a v htc hc
    rcases indCont_next hc with ⟨hc1, -⟩ | ⟨hc1, -⟩
    · exact .inr (.inl ⟨_, by rw [hc1, htc]⟩)
    · exact .inl (by rw [hc1, htc])
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env p s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hcall (tryState s bc) [] _ ext vals rfl h
  · rw [step_tryInd env p s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    obtain ⟨⟨d, a, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hind (tryState s bc) [] _ _ d a v rfl h
  · rw [step_ind env p s hb hi] at h
    obtain ⟨⟨d, a, v⟩, -, h⟩ := Opt.StepResult.ofRes_eq_next h
    exact hind s rest st.results sig d a v rfl h
  · rw [Opt.step_eq_lift env p s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | next fr1 m1 => rw [hl] at h; cases h; exact .inl rfl
    | call ext vals rs rest => rw [hl] at h; exact hcall s rest rs ext vals rfl h
    | ret vals =>
      rw [hl] at h
      obtain ⟨c, rs, cs, regs, hc, hc1, -⟩ := returnValues_next h
      exact .inr (.inr ⟨(c, rs), by rw [hc, hc1]⟩)
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI)
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- A step that finishes the run returns from a frame without callers. -/
theorem step_done_callers {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    {s : State} {v : List Val} {m : Mem} (hI : LFrame P s.frame) (h : step env p s = .done v m) :
    s.callers = [] := by
  rcases step_shape s with ⟨fn, args, et, hb, ht⟩ | ⟨callee, args, et, hb, ht⟩ |
    ⟨st, rest, sig, callee, args, hb, hi⟩ | hci
  · rw [step_try env p s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨ext, vals⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h callCont_ne_done
  · rw [step_tryInd env p s hb ht] at h
    obtain ⟨⟨n, b, bc⟩, -, h⟩ := ofRes_eq_done h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [step_ind env p s hb hi] at h
    obtain ⟨⟨d, a, w⟩, -, h⟩ := ofRes_eq_done h
    exact absurd h indCont_ne_done
  · rw [Opt.step_eq_lift env p s hci] at h
    cases hl : Opt.lstep s.frame s.mem with
    | ret vals =>
      rw [hl] at h
      exact (returnValues_done h).1
    | call ext vals rs rest => rw [hl] at h; exact absurd h callCont_ne_done
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI)
    | next fr1 m1 => rw [hl] at h; cases h
    | trap c => rw [hl] at h; cases h
    | stuck m => rw [hl] at h; cases h

/-- `liftStep` with callers below the stack, for a step that keeps the stack shape
(`CallersStep`) and finishes only without callers. -/
theorem liftStep_below (xs : XState) (r : StepResult) (M : List (Frame × List ValueId))
    (T : List (Option ExnTable)) (ha : xs.Aligned)
    (hr : ∀ s1, r = .next s1 → CallersStep xs.s.callers s1.callers)
    (hd : ∀ v m, r = .done v m → xs.s.callers = []) :
    liftStep (xs.below M T) (r.below M) = (liftStep xs r).below M T := by
  cases r with
  | next s1 =>
    simp only [StepResult.below, liftStep, XStepResult.below, XState.below, State.below_callers,
      List.length_append, pendingOf_below, XStepResult.next.injEq, XState.mk.injEq, true_and]
    unfold XState.Aligned at ha
    rcases hr s1 rfl with h | ⟨c, h⟩ | ⟨c, h⟩
    · rw [h]
      (repeat' split) <;> first | rfl | omega | simp_all
    · rw [h]
      simp only [List.length_cons]
      (repeat' split) <;> first | rfl | omega | simp_all
    · rw [h] at ha ⊢
      simp only [List.length_cons] at ha ⊢
      cases ht : xs.tries with
      | nil => rw [ht] at ha; simp at ha
      | cons t ts => (repeat' split) <;> first | rfl | omega | simp_all
  | done v m =>
    have hc := hd v m rfl
    have hnil : xs.tries = [] := by
      unfold XState.Aligned at ha; rw [hc] at ha; exact List.length_eq_zero_iff.mp ha
    simp only [StepResult.below, liftStep, XStepResult.below, resumeStepX]
    cases M with
    | nil => rfl
    | cons cr cs =>
      obtain ⟨c, rs⟩ := cr
      cases hset : c.regs.setMany rs v with
      | none => simp only [resumeStep, hset]
      | some regs =>
        simp only [resumeStep, hset, XState.below, State.below_callers, hc, hnil,
          List.nil_append, List.length_cons]
        (repeat' split) <;> first | rfl | omega | simp_all
  | trapped c => rfl
  | stuck m => rfl

/-! ## The invariant of whole-program states -/

/-- Every frame runs a function of `P` (`LInv`), and the pending tables are aligned with the
callers. -/
def XInv (P : Program) (xs : XState) : Prop := LInv P xs.s ∧ xs.Aligned

theorem catchIn_ok {fr fr' : Frame} {et : ExnTable} {e : Exn}
    (h : catchIn fr et e = some (.ok fr')) :
    ∃ regs bc, fr' = { fr with regs, body := [], term := .jump bc } := by
  simp only [catchIn, Option.map_eq_some_iff] at h
  obtain ⟨d, -, h⟩ := h
  cases hb : tryHandler d fr.func.freshValue with
  | ok bc =>
    rw [hb, Res.ok_bind] at h
    cases hs : fr.regs.setMany ((List.range e.payload.length).map (fr.func.freshValue + ·))
        e.payload with
    | none => rw [hs] at h; cases h
    | some regs =>
      rw [hs] at h
      simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq, Res.ok.injEq] at h
      exact ⟨regs, bc, h.symm⟩
  | trap c => rw [hb] at h; cases h
  | stuck m => rw [hb] at h; cases h

/-- An exception caught by a suspended caller: the `k`-th caller resumes at its handler. -/
theorem unwindFrom_next (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (xs' : XState), unwindFrom e fr cs ts mem = .next xs' →
      ∃ k c rs regs bc, cs[k]? = some (c, rs) ∧ xs'.s.callers = cs.drop (k + 1) ∧
        xs'.tries = ts.drop (k + 1) ∧ xs'.s.frame = { c with regs, body := [], term := .jump bc }
  | fr, [], _, mem, xs', h => by simp [unwindFrom] at h
  | fr, (c, rs) :: cs, t :: ts, mem, xs', h => by
    simp only [unwindFrom] at h
    split at h
    · rename_i r hr
      cases r with
      | ok fr' =>
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
        exact ⟨0, c, rs, regs, bc, rfl, rfl, rfl, rfl⟩
      | trap c => simp [XStepResult.ofRes] at h
      | stuck m => simp [XStepResult.ofRes] at h
    · obtain ⟨k, c', rs', regs, bc, h1, h2, h3, h4⟩ := unwindFrom_next e c cs ts _ xs' h
      exact ⟨k + 1, c', rs', regs, bc, by simpa using h1, by simpa using h2, by simpa using h3, h4⟩
  | fr, _ :: _, [], mem, xs', h => by simp [unwindFrom] at h

theorem LInv.with_mem {P : Program} {s : State} (h : LInv P s) (mem : Mem) :
    LInv P { s with mem } := h

/-- A step of the run with unwinding keeps `XInv` (for a program whose functions are `P`'s). -/
theorem stepX_next_xinv {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs xs' : XState} (hI : XInv P xs) (h : stepX env p xs = .next xs')
    (hp : ∀ g ∈ p.funcs, g ∈ P.funcs := by exact fun _ h => h) : XInv P xs' := by
  unfold stepX at h
  split at h
  · rename_i e mem _
    unfold raiseIn at h
    split at h
    · rename_i r hr
      cases r with
      | ok fr =>
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
        exact ⟨⟨LFrame.jump hI.1.1.1 regs bc, hI.1.2⟩, hI.2⟩
      | trap c => simp [XStepResult.ofRes] at h
      | stuck m => simp [XStepResult.ofRes] at h
    · obtain ⟨k, c, rs, regs, bc, hk, h1, h2, h3⟩ := unwindFrom_next e _ _ _ _ xs' h
      have hcm : (c, rs) ∈ xs.s.callers := List.mem_of_getElem? hk
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h3]; exact LFrame.jump (hI.1.2 _ hcm).1 regs bc
      · rw [h1]; exact fun c' hc' => hI.1.2 c' (List.mem_of_mem_drop hc')
      · unfold XState.Aligned
        rw [h1, h2, List.length_drop, List.length_drop, hI.2]
  · cases hs : step env.toEnv p xs.s with
    | next s1 =>
      rw [hs] at h
      simp only [liftStep, XStepResult.next.injEq] at h
      subst h
      refine ⟨(step_next_linv hP hI.1 hs hp).1, ?_⟩
      have ha := hI.2
      unfold XState.Aligned at ha ⊢
      simp only
      rcases step_callers hP hI.1.1 hs with hc | ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; (repeat' split) <;> first | omega | exact ha | simp_all
      · rw [hc]
        simp only [List.length_cons]
        (repeat' split) <;> first | omega | (simp [ha]; done) | simp_all
      · rw [hc] at ha ⊢
        simp only [List.length_cons] at ha ⊢
        (repeat' split) <;> first | omega | (simp [List.length_tail, ha]; done) | simp_all
    | _ => rw [hs] at h; simp [liftStep] at h

/-- `stepX` with callers below the stack, from a state of the invariant. -/
theorem stepX_below {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs : XState} (hI : XInv P xs) (M : List (Frame × List ValueId))
    (T : List (Option ExnTable)) :
    stepX env p (xs.below M T) = (stepX env p xs).below M T := by
  unfold stepX
  rw [show (xs.below M T).s = xs.s.below M from rfl, raiseAt?_below]
  split
  · exact raiseIn_below xs _ _ M T hI.2
  · rw [step_below]
    exact liftStep_below xs _ M T hI.2 (fun s1 h => step_callers hP hI.1.1 h)
      (fun v m h => step_done_callers hP hI.1.1 h)

/-! ## Runs with more callers below the stack -/

/-- What `runLoopX` does after a step, with `fuel` left. -/
def afterStepX (env : XEnv) (p : Program) (fuel : Nat) : XStepResult → XOutcome
  | .next xs' => runLoopX env p fuel xs'
  | .done vals mem => .returned vals mem
  | .unwound e mem => .unwound e mem
  | .trapped c => .trapped c
  | .stuck m => .stuck m

theorem runLoopX_succ' (env : XEnv) (p : Program) (fuel : Nat) (xs : XState) :
    runLoopX env p (fuel + 1) xs = afterStepX env p fuel (stepX env p xs) := by
  cases h : stepX env p xs <;> simp [runLoopX, h, afterStepX]

/-- A run that neither returns nor unwinds out of its bottom frame within the fuel is the same
run with more callers below the stack. -/
theorem runLoopX_below_of_not_ended {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) (env : XEnv)
    (M : List (Frame × List ValueId)) (T : List (Option ExnTable)) :
    ∀ (N : Nat) (xs : XState), XInv P xs →
      (∀ vals mem, runLoopX env P N xs ≠ .returned vals mem) →
      (∀ e mem, runLoopX env P N xs ≠ .unwound e mem) →
      runLoopX env P N (xs.below M T) = runLoopX env P N xs
  | 0, _, _, _, _ => rfl
  | N + 1, xs, hI, h1, h2 => by
    rw [runLoopX_succ', runLoopX_succ', stepX_below hP hI]
    rw [runLoopX_succ'] at h1 h2
    cases hs : stepX env P xs with
    | next xs' =>
      rw [hs] at h1 h2
      exact runLoopX_below_of_not_ended hP env M T N xs' (stepX_next_xinv hP hI hs) h1 h2
    | done vals mem => rw [hs] at h1; exact absurd rfl (h1 vals mem)
    | unwound e mem => rw [hs] at h2; exact absurd rfl (h2 e mem)
    | trapped c => rfl
    | stuck m => rfl

/-- **The bottom frame returns**: with callers `M` (tables `T`) below, the run is at
`resumeStepX M T vals mem` after the same number of steps. -/
theorem runLoopX_below_returned {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) (env : XEnv) :
    ∀ (N : Nat) (xs : XState) (vals : List Val) (mem : Mem), XInv P xs →
      runLoopX env P N xs = .returned vals mem →
      ∃ j, 0 < j ∧ j ≤ N ∧ ∀ (M : List (Frame × List ValueId)) (T : List (Option ExnTable))
        (n : Nat), runLoopX env P (n + j) (xs.below M T) = afterStepX env P n (resumeStepX M T vals mem)
  | 0, _, _, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, vals, mem, hI, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env P xs with
    | next xs' =>
      rw [hs] at h
      obtain ⟨j, hj0, hjN, hr⟩ :=
        runLoopX_below_returned hP env N xs' vals mem (stepX_next_xinv hP hI hs) h
      refine ⟨j + 1, by omega, by omega, fun M T n => ?_⟩
      rw [show n + (j + 1) = (n + j) + 1 by omega, runLoopX_succ', stepX_below hP hI, hs]
      exact hr M T n
    | done vals' mem' =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨1, by omega, by omega, fun M T n => ?_⟩
      rw [runLoopX_succ', stepX_below hP hI, hs]
      rfl
    | unwound e m => rw [hs] at h; cases h
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-- **The bottom frame is left by an exception**: with callers `M` (tables `T`) below, the run is
at `resumeUnwind e M T mem` after the same number of steps. -/
theorem runLoopX_below_unwound {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) (env : XEnv) :
    ∀ (N : Nat) (xs : XState) (e : Exn) (mem : Mem), XInv P xs →
      runLoopX env P N xs = .unwound e mem →
      ∃ j, 0 < j ∧ j ≤ N ∧ ∀ (M : List (Frame × List ValueId)) (T : List (Option ExnTable))
        (n : Nat), runLoopX env P (n + j) (xs.below M T) = afterStepX env P n (resumeUnwind e M T mem)
  | 0, _, _, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, e, mem, hI, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env P xs with
    | next xs' =>
      rw [hs] at h
      obtain ⟨j, hj0, hjN, hr⟩ :=
        runLoopX_below_unwound hP env N xs' e mem (stepX_next_xinv hP hI hs) h
      refine ⟨j + 1, by omega, by omega, fun M T n => ?_⟩
      rw [show n + (j + 1) = (n + j) + 1 by omega, runLoopX_succ', stepX_below hP hI, hs]
      exact hr M T n
    | unwound e' mem' =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨1, by omega, by omega, fun M T n => ?_⟩
      rw [runLoopX_succ', stepX_below hP hI, hs]
      rfl
    | done v m => rw [hs] at h; cases h
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-- More fuel does not change a run that ended. -/
theorem runLoopX_add (env : XEnv) (p : Program) :
    ∀ (N : Nat) (xs : XState), runLoopX env p N xs ≠ .outOfFuel →
      ∀ k, runLoopX env p (N + k) xs = runLoopX env p N xs
  | 0, _, h, _ => absurd rfl h
  | N + 1, xs, h, k => by
    rw [show N + 1 + k = (N + k) + 1 by omega, runLoopX_succ', runLoopX_succ']
    rw [runLoopX_succ'] at h
    cases hs : stepX env p xs with
    | next xs' =>
      rw [hs] at h
      exact runLoopX_add env p N xs' h k
    | _ => rfl

open Classical in
/-- The outcome of a run with unwinding with unbounded fuel. -/
noncomputable def runLimX (env : XEnv) (p : Program) (xs : XState) : XOutcome :=
  if h : ∃ n, runLoopX env p n xs ≠ .outOfFuel then runLoopX env p (Classical.choose h) xs
  else .outOfFuel

theorem runLimX_eq {env : XEnv} {p : Program} {xs : XState} {n : Nat}
    (h : runLoopX env p n xs ≠ .outOfFuel) : runLimX env p xs = runLoopX env p n xs := by
  unfold runLimX
  split
  · rename_i hex
    have hc := Classical.choose_spec hex
    rw [← runLoopX_add env p _ xs hc n, Nat.add_comm, runLoopX_add env p n xs h]
  · rename_i hn
    exact absurd ⟨n, h⟩ hn

/-! ## The bottom frame and the return types -/

theorem unwindFrom_ne_done (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (v : List Val) (m : Mem), unwindFrom e fr cs ts mem ≠ .done v m
  | fr, [], _, mem, v, m, h => by simp [unwindFrom] at h
  | fr, (c, rs) :: cs, t :: ts, mem, v, m, h => by
    simp only [unwindFrom] at h
    split at h
    · rename_i r _
      cases r <;> simp [XStepResult.ofRes] at h
    · exact unwindFrom_ne_done e c cs ts _ v m h
  | fr, _ :: _, [], mem, v, m, h => by simp [unwindFrom] at h

/-- A step with unwinding that finishes the run is a finishing step of `Clif.step`. -/
theorem stepX_done_inv {env : XEnv} {p : Program} {xs : XState} {v : List Val} {m : Mem}
    (h : stepX env p xs = .done v m) : step env.toEnv p xs.s = .done v m := by
  unfold stepX at h
  split at h
  · unfold raiseIn at h
    split at h
    · rename_i r _
      cases r <;> simp [XStepResult.ofRes] at h
    · exact absurd h (unwindFrom_ne_done _ _ _ _ _ v m)
  · cases hs : step env.toEnv p xs.s <;> rw [hs] at h <;> simp [liftStep] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem getLast?_drop_succ {α : Type} :
    ∀ {l : List α} {k : Nat} {x : α}, l[k]? = some x →
      (l.drop (k + 1)).getLast? = l.getLast? ∨ (l.drop (k + 1) = [] ∧ l.getLast? = some x)
  | [], _, _, h => by simp at h
  | [a], 0, x, h => by simp at h; subst h; right; simp
  | [a], k + 1, x, h => by simp at h
  | a :: b :: l, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    left
    simp [List.getLast?_cons_cons]
  | a :: b :: l, k + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    rcases getLast?_drop_succ (l := b :: l) h with h1 | ⟨h1, h2⟩
    · left
      rw [List.drop_succ_cons, h1, List.getLast?_cons_cons]
    · right
      rw [List.drop_succ_cons, h1, List.getLast?_cons_cons, h2]
      exact ⟨rfl, rfl⟩

/-- A step with unwinding keeps the function of the bottom frame. -/
theorem stepX_next_bottom {P p : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    {xs xs' : XState} (hI : XInv P xs) (h : stepX env p xs = .next xs')
    (hp : ∀ g ∈ p.funcs, g ∈ P.funcs := by exact fun _ h => h) : xs'.s.bottom = xs.s.bottom := by
  unfold stepX at h
  split at h
  · rename_i e mem _
    unfold raiseIn at h
    split at h
    · rename_i r hr
      cases r with
      | ok fr =>
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
        rfl
      | trap c => simp [XStepResult.ofRes] at h
      | stuck m => simp [XStepResult.ofRes] at h
    · obtain ⟨k, c, rs, regs, bc, hk, h1, -, h3⟩ := unwindFrom_next e _ _ _ _ xs' h
      unfold State.bottom
      rw [h1, h3]
      rcases getLast?_drop_succ hk with h4 | ⟨h4, h5⟩
      · rw [h4]
        cases hl : xs.s.callers.getLast? with
        | none =>
          rw [List.getLast?_eq_none_iff] at hl
          rw [hl] at hk; simp at hk
        | some y => rfl
      · rw [h4, h5]
        rfl
  · cases hs : step env.toEnv p xs.s with
    | next s1 =>
      rw [hs] at h
      simp only [liftStep, XStepResult.next.injEq] at h
      subst h
      exact (step_next_linv hP hI.1 hs hp).2
    | _ => rw [hs] at h; simp [liftStep] at h

/-- **Return types**: a whole-program run with unwinding that returns gives values of the bottom
frame's return types. -/
theorem runLoopX_returned_tys {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv} :
    ∀ (N : Nat) (xs : XState) (vals : List Val) (mem : Mem), XInv P xs →
      runLoopX env P N xs = .returned vals mem →
      vals.map (·.ty) = AbiParam.tys xs.s.bottom.sig.returns
  | 0, _, _, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, vals, mem, hI, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env P xs with
    | next xs' =>
      rw [hs] at h
      rw [runLoopX_returned_tys hP N xs' vals mem (stepX_next_xinv hP hI hs) h,
        stepX_next_bottom hP hI hs]
    | done v m =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hc, ht⟩ := step_done_linv hP hI.1 (stepX_done_inv hs)
      rw [ht]
      simp [State.bottom, hc]
    | unwound e m => rw [hs] at h; cases h
    | trapped c => rw [hs] at h; cases h
    | stuck m => rw [hs] at h; cases h

/-! ## The linked environment with unwinding -/

/-- **The environment of the per-function programs of `P` with unwinding**: a call of a function
`g` of `P` runs `g`'s whole-program run with unwinding (unbounded fuel, `runLimX`) — an
exception that leaves `g` is the extern's exceptional result; every other extern is `env`'s. -/
noncomputable def linkEnvX (P : Program) (env : XEnv) : XEnv where
  extern n := match P.func? n with
    | some _ => some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLimX env P s.toX
      | .trap c => .trapped c
      | .stuck m => .stuck m
    | none => env.extern n
  names := env.names
  sigOf := env.sigOf

theorem linkEnvX_none {P : Program} {env : XEnv} {n : String} (h : P.func? n = none) :
    (linkEnvX P env).extern n = env.extern n := by
  simp [linkEnvX, h]

theorem linkEnvX_some {P : Program} {env : XEnv} {n : String} {g : Function}
    (h : P.func? n = some g) :
    (linkEnvX P env).extern n = some fun vals mem =>
      match initState P n vals mem with
      | .ok s => runLimX env P s.toX
      | .trap c => .trapped c
      | .stuck m => .stuck m := by
  simp [linkEnvX, h]

theorem linkEnvX_toEnv_none {P : Program} {env : XEnv} {n : String} (h : P.func? n = none) :
    (linkEnvX P env).toEnv.extern n = env.toEnv.extern n := by
  simp [XEnv.toEnv, linkEnvX_none h]

/-! ## Raising at a call -/

/-- The exception the call of `ext` on `vals` from `mem` raises (after `callRaise`'s prelude). -/
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
    callRaise env p mem fr fn args = match Opt.callArgs fr fn args with
      | .ok (ext, vals) => extRaise env p mem ext vals
      | _ => none := by
  unfold callRaise Opt.callArgs extRaise
  rfl

theorem tryCallRaise_eq (env : XEnv) (p : Program) (mem : Mem) (fr : Frame) (fn : FnRef)
    (args : List ValueId) (et : ExnTable) :
    tryCallRaise env p mem fr fn args et = match tryPre fr fn et with
      | .ok _ => callRaise env p mem fr fn args
      | _ => none := by
  unfold tryCallRaise tryPre
  rfl

theorem catchIn_congr {fr fr' : Frame} (hf : fr'.func = fr.func) (hr : fr'.regs = fr.regs)
    (hs : fr'.slots = fr.slots) (et : ExnTable) (e : Exn) : catchIn fr' et e = catchIn fr et e := by
  obtain ⟨f1, r1, s1, b1, t1⟩ := fr
  obtain ⟨f2, r2, s2, b2, t2⟩ := fr'
  simp only at hf hr hs
  subst hf hr hs
  rfl

theorem unwindFrom_congr {fr fr' : Frame} (hs : fr'.slots = fr.slots) (e : Exn)
    (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem) :
    unwindFrom e fr' cs ts mem = unwindFrom e fr cs ts mem := by
  rw [unwindFrom_eq, unwindFrom_eq, hs]

/-- Raising at the call of a frame is the exception leaving a callee entered from it: the caller
(the frame with the call done, `c`) consults the pending table of the call. -/
theorem raiseIn_eq_resumeUnwind {xs : XState} {c : Frame} (rs : List ValueId) (e : Exn)
    (mem : Mem) (hf : c.func = xs.s.frame.func) (hr : c.regs = xs.s.frame.regs)
    (hs : c.slots = xs.s.frame.slots) :
    raiseIn xs e mem = resumeUnwind e ((c, rs) :: xs.s.callers) (pendingOf xs.s :: xs.tries) mem := by
  unfold raiseIn
  simp only [resumeUnwind]
  rw [show (fun x => catchIn c x e) = (fun x => catchIn xs.s.frame x e) from
    funext fun et => catchIn_congr hf hr hs et e]
  cases (pendingOf xs.s).bind (fun x => catchIn xs.s.frame x e) with
  | some r => rfl
  | none => exact (unwindFrom_congr hs e _ _ mem).symm

/-- A raise of an extern outside `P` (the base environment's) is the same raise in the
per-function program under `linkEnvX`. -/
theorem raiseAt_link {P : Program} {env : XEnv} {f : Function} (hf : f ∈ P.funcs)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hIF : ∀ g ∈ P.funcs, IndFree g) {s : State}
    (hI : LFrame P s.frame) {em : Exn × Mem} (h : raiseAt? env P s = some em) :
    raiseAt? (linkEnvX P env) (P.only f) s = some em := by
  have hbase : ∀ ext vals, extRaise env P s.mem ext vals = some em →
      extRaise (linkEnvX P env) (P.only f) s.mem ext vals = some em := by
    intro ext vals h
    unfold extRaise at h ⊢
    cases hp : P.func? ext.name with
    | some g => rw [hp] at h; cases h
    | none =>
      rw [hp] at h
      have hfn : f.name ≠ ext.name := Program.func?_none hp f hf
      simp only [Program.only_func?, hfn, ↓reduceIte, linkEnvX_none hp]
      exact h
  have hcall : ∀ fn args, callRaise env P s.mem s.frame fn args = some em →
      callRaise (linkEnvX P env) (P.only f) s.mem s.frame fn args = some em := by
    intro fn args h
    rw [callRaise_eq] at h ⊢
    cases hc : Opt.callArgs s.frame fn args with
    | ok q => obtain ⟨ext, vals⟩ := q; rw [hc] at h; exact hbase ext vals h
    | trap c => rw [hc] at h; cases h
    | stuck m => rw [hc] at h; cases h
  revert h
  unfold raiseAt?
  cases hb : s.frame.body with
  | cons st rest =>
    dsimp only
    cases hi : st.inst with
    | call fn args => dsimp only; exact hcall fn args
    | callIndirect sig callee args =>
      intro _
      obtain ⟨B, hB, hsuf, -⟩ | ⟨hnil, -⟩ := hI.2
      · exact absurd hi ((hIF _ hI.1 B hB).1 st (hsuf.subset (by rw [hb]; simp)) sig callee args)
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
      | ok q => rw [hp] at h; exact hcall fn args h
      | trap c => rw [hp] at h; cases h
      | stuck m => rw [hp] at h; cases h
    | tryCallIndirect callee args et =>
      intro _
      obtain ⟨B, hB, -, hbt⟩ | ⟨-, bc, hbt⟩ := hI.2
      · exact absurd (hbt.symm.trans ht) ((hIF _ hI.1 B hB).2 callee args et)
      · rw [hbt] at ht; cases ht
    | _ => dsimp only; intro h; cases h

theorem callArgs_tryState (s : State) (bc : BlockCall) (fn : FnRef) (args : List ValueId) :
    Opt.callArgs (tryState s bc).frame fn args = Opt.callArgs s.frame fn args := by
  simp only [Opt.callArgs, tryState, Frame.getMany_with]

/-- No call is raising at a step that `lstep` does not make a call (and that is no indirect
call, `try_call` or tail call). -/
theorem raiseAt_none_of_lstep {env : XEnv} {p P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g)
    {s : State} (hI : LFrame P s.frame) (hci : Opt.HeadNoCI s.frame)
    (hl : ∀ ext vals rs rest, Opt.lstep s.frame s.mem ≠ .call ext vals rs rest) :
    raiseAt? env p s = none := by
  unfold raiseAt?
  cases hb : s.frame.body with
  | cons st rest =>
    dsimp only
    cases hi : st.inst with
    | call fn args =>
      dsimp only
      rw [callRaise_eq]
      cases hc : Opt.callArgs s.frame fn args with
      | ok q =>
        obtain ⟨ext, vals⟩ := q
        exact absurd (by rw [Opt.lstep_call hb hi, hc]; rfl) (hl ext vals st.results rest)
      | trap c => rfl
      | stuck m => rfl
    | callIndirect sig callee args => exact absurd hi (hci.1 st rest hb sig callee args)
    | _ => rfl
  | nil =>
    dsimp only
    have hnt := hci.2 hb
    cases ht : s.frame.term with
    | returnCall fn args =>
      obtain ⟨B, hB, -, hbt⟩ | ⟨-, bc, hbt⟩ := hI.2
      · exact absurd (hbt.symm.trans ht) (hP _ hI.1 B hB fn args)
      · rw [hbt] at ht; cases ht
    | tryCall fn args et => rw [ht] at hnt; cases hnt
    | tryCallIndirect callee args et => rw [ht] at hnt; cases hnt
    | _ => rfl

/-! ## The linking theorem (CLIF, with unwinding) -/

theorem afterStepX_fuel {env : XEnv} {p : Program} {r : XStepResult} (h : ∀ xs1, r ≠ .next xs1)
    (n n' : Nat) : afterStepX env p n r = afterStepX env p n' r := by
  cases r with
  | next xs1 => exact absurd rfl (h xs1)
  | _ => rfl

/-- **Linking at the CLIF level with unwinding.** For a program `P` with distinct function names
whose functions have no `call_indirect`, `try_call_indirect` (`IndFree`) or `return_call`
(`LinkFree`), a whole-program run with unwinding from a state of `P`'s frames with aligned
pending tables (`XInv`) that returns, traps or unwinds within `N` steps is a per-function run of
`P.only f` (only `f` is entered; a call of another function `g` of `P` is atomic, `linkEnvX`:
`g`'s whole-program run, an exception leaving `g` being raised at the call) with the same
outcome. -/
theorem runLoopX_link {P : Program} {env : XEnv} {f : Function}
    (hnd : (P.funcs.map (·.name)).Nodup) (hf : f ∈ P.funcs) (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hIF : ∀ g ∈ P.funcs, IndFree g) :
    ∀ (N : Nat) (xs : XState), XInv P xs →
      (∀ msg, runLoopX env P N xs ≠ .stuck msg) → runLoopX env P N xs ≠ .outOfFuel →
      ∃ m, runLoopX (linkEnvX P env) (P.only f) m xs = runLoopX env P N xs := by
  have hpf : ∀ g ∈ (P.only f).funcs, g ∈ P.funcs := fun g hg => by
    simp only [Program.only, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hf
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro xs hI hst hof
  cases N with
  | zero => exact absurd rfl hof
  | succ N =>
  -- a per-function step `r` after which the whole-program run continues with `n` steps
  have helper : ∀ (r : XStepResult) (n : Nat), n < N + 1 →
      stepX (linkEnvX P env) (P.only f) xs = r → runLoopX env P (N + 1) xs = afterStepX env P n r →
      ∃ m, runLoopX (linkEnvX P env) (P.only f) m xs = runLoopX env P (N + 1) xs := by
    intro r n hn hr hrun
    cases r with
    | next xs1 =>
      rw [hrun] at hst hof ⊢
      obtain ⟨m, hm⟩ := ih n hn xs1 (stepX_next_xinv hP hI hr hpf) hst hof
      exact ⟨m + 1, by rw [runLoopX_succ', hr]; exact hm⟩
    | _ => exact ⟨0 + 1, by rw [runLoopX_succ', hr, hrun]; rfl⟩
  -- the steps that do not call another function of `P` are the same
  have same : stepX (linkEnvX P env) (P.only f) xs = stepX env P xs →
      ∃ m, runLoopX (linkEnvX P env) (P.only f) m xs = runLoopX env P (N + 1) xs := fun h =>
    helper _ N (by omega) h (runLoopX_succ' ..)
  -- a raise of a base extern is the same raise
  cases hra : raiseAt? env P xs.s with
  | some em =>
    exact same (by simp only [stepX, raiseAt_link hf hP hIF hI.1.1 hra, hra])
  | none =>
  have ew : stepX env P xs = liftStep xs (step env.toEnv P xs.s) := by simp only [stepX, hra]
  -- a call (`callCont`) from `t`, whose frame is `xs`'s up to `body`/`term`
  have call : ∀ (t : State) rest rs ext vals, t.callers = xs.s.callers → t.mem = xs.s.mem →
      t.frame.func = xs.s.frame.func → t.frame.regs = xs.s.frame.regs →
      t.frame.slots = xs.s.frame.slots →
      (∀ regs, LFrame P { t.frame with regs, body := rest }) →
      step env.toEnv P xs.s = Opt.callCont env.toEnv P t rest rs ext vals →
      step (linkEnvX P env).toEnv (P.only f) xs.s =
        Opt.callCont (linkEnvX P env).toEnv (P.only f) t rest rs ext vals →
      raiseAt? (linkEnvX P env) (P.only f) xs.s = extRaise (linkEnvX P env) (P.only f) xs.s.mem ext vals →
      extRaise env P xs.s.mem ext vals = none →
      ∃ m, runLoopX (linkEnvX P env) (P.only f) m xs = runLoopX env P (N + 1) xs := by
    intro t rest rs ext vals htc htm htf htr hts hfr e1 e2 e3 hw
    cases hpf' : P.func? ext.name with
    | none =>
      have hfn : f.name ≠ ext.name := Program.func?_none hpf' f hf
      have hx : extRaise (linkEnvX P env) (P.only f) xs.s.mem ext vals = none := by
        rw [← hw]
        unfold extRaise
        simp only [Program.only_func?, hfn, ↓reduceIte, linkEnvX_none hpf', hpf']
      apply same
      simp only [stepX, e3, hx, hra, e1, e2]
      simp only [Opt.callCont, hpf', Program.only_func?, hfn, ↓reduceIte, linkEnvX_toEnv_none hpf']
    | some g =>
      obtain ⟨hgP, hgn⟩ := Program.func?_some hpf'
      by_cases hgf : g = f
      · subst hgf
        have hx : extRaise (linkEnvX P env) (P.only g) xs.s.mem ext vals = none := by
          unfold extRaise
          simp only [Program.only_func?, hgn, ↓reduceIte]
        apply same
        simp only [stepX, e3, hx, hra, e1, e2]
        simp only [Opt.callCont, hpf', Program.only_func?, hgn, ↓reduceIte]
      have hfn : f.name ≠ ext.name := fun h => hgf (name_inj hnd hgP hf (hgn.trans h.symm))
      -- the whole-program step: `g` entered
      cases hsig : (AbiParam.tys g.sig.params == AbiParam.tys ext.sig.params &&
          AbiParam.tys g.sig.returns == AbiParam.tys ext.sig.returns) with
      | false =>
        obtain ⟨msg, hm⟩ : ∃ msg, stepX env P xs = .stuck msg := by
          rw [ew, e1]
          simp only [Opt.callCont, hpf', hsig, Bool.false_eq_true, ↓reduceIte, liftStep]
          exact ⟨_, rfl⟩
        rw [runLoopX_succ', hm] at hst
        exact absurd rfl (hst msg)
      | true =>
        have hsig2 := hsig
        simp only [Bool.and_eq_true, beq_iff_eq] at hsig2
        cases he : enterFunc g vals t.mem with
        | trap c => exact absurd he (Opt.enterFunc_not_trap g vals t.mem c)
        | stuck m =>
          have hm : stepX env P xs = .stuck m := by
            rw [ew, e1]
            simp only [Opt.callCont, hpf', hsig, ↓reduceIte, he, StepResult.ofRes, liftStep]
          rw [runLoopX_succ', hm] at hst
          exact absurd rfl (hst m)
        | ok a =>
          obtain ⟨fr', mem'⟩ := a
          let K : List (Frame × List ValueId) := ({ t.frame with body := rest }, rs) :: xs.s.callers
          let T : List (Option ExnTable) := pendingOf xs.s :: xs.tries
          let sub : XState := ⟨⟨fr', [], mem'⟩, []⟩
          have hw1 : stepX env P xs = .next (sub.below K T) := by
            rw [ew, e1]
            simp only [Opt.callCont, hpf', hsig, ↓reduceIte, he, StepResult.ofRes, liftStep, htc,
              List.length_cons]
            rfl
          have hwN : runLoopX env P (N + 1) xs = runLoopX env P N (sub.below K T) := by
            rw [runLoopX_succ', hw1]; rfl
          rw [hwN] at hst hof ⊢
          have hsubI : XInv P sub := ⟨⟨LFrame.enterFunc hgP he, fun _ h => by cases h⟩, rfl⟩
          have hfr' : fr'.func = g := by
            obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
            rw [hfr]
          have hinit : initState P ext.name vals t.mem = .ok ⟨fr', [], mem'⟩ := by
            simp [initState, hpf', he, Res.ofOption, bind, Res.bind, pure]
          -- the per-function step: the atomic call of `g`
          have hext : extRaise (linkEnvX P env) (P.only f) xs.s.mem ext vals =
              match runLimX env P sub with
              | .unwound e m => some (e, m)
              | _ => none := by
            unfold extRaise
            simp only [Program.only_func?, hfn, ↓reduceIte, linkEnvX_some hpf', ← htm, hinit]
            rfl
          have hcc : Opt.callCont (linkEnvX P env).toEnv (P.only f) t rest rs ext vals =
              match (runLimX env P sub).toOutcome with
              | .returned rvals mem' =>
                if rvals.map (·.ty) == AbiParam.tys ext.sig.returns then
                  continueWith t rest rs rvals mem'
                else .stuck s!"extern %{ext.name} returned values of the wrong types"
              | .trapped c => .trapped c
              | .stuck m => .stuck m
              | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel" := by
            simp only [Opt.callCont, Program.only_func?, hfn, ↓reduceIte, XEnv.toEnv,
              linkEnvX_some hpf', Option.map_some, hinit]
            rfl
          cases hsub : runLoopX env P N sub with
          | returned rvals mem2 =>
            obtain ⟨j, hj0, hjN, hj⟩ := runLoopX_below_returned hP env N sub rvals mem2 hsubI hsub
            have hjj := hj K T (N - j)
            rw [show N - j + j = N by omega] at hjj
            rw [hjj] at hst hof ⊢
            have hlim : runLimX env P sub = .returned rvals mem2 :=
              (runLimX_eq (n := N) (by rw [hsub]; exact fun h => by cases h)).trans hsub
            have hty := runLoopX_returned_tys hP N sub rvals mem2 hsubI hsub
            simp only [sub, State.bottom, List.getLast?_nil, Option.map_none, Option.getD_none,
              hfr'] at hty
            cases hset : t.frame.regs.setMany rs rvals with
            | none =>
              simp only [resumeStepX, resumeStep, K, hset, afterStepX] at hst
              exact absurd rfl (hst _)
            | some regs =>
              have hres : resumeStepX K T rvals mem2 =
                  .next ⟨⟨{ t.frame with regs, body := rest }, xs.s.callers, mem2⟩, xs.tries⟩ := by
                simp only [resumeStepX, resumeStep, K, T, hset, List.tail_cons]
              rw [hres] at hst hof ⊢
              simp only [afterStepX] at hst hof ⊢
              have hpstep : stepX (linkEnvX P env) (P.only f) xs =
                  .next ⟨⟨{ t.frame with regs, body := rest }, xs.s.callers, mem2⟩, xs.tries⟩ := by
                simp only [stepX, e3, hext, hlim, e2, hcc, XOutcome.toOutcome, hty, hsig2.2,
                  beq_self_eq_true, ↓reduceIte, continueWith, hset, liftStep, htc]
                simp
              obtain ⟨m, hm⟩ := ih (N - j) (by omega)
                ⟨⟨{ t.frame with regs, body := rest }, xs.s.callers, mem2⟩, xs.tries⟩
                ⟨⟨hfr regs, hI.1.2⟩, hI.2⟩ hst hof
              exact ⟨m + 1, by rw [runLoopX_succ', hpstep]; exact hm⟩
          | unwound e2 mem2 =>
            obtain ⟨j, hj0, hjN, hj⟩ := runLoopX_below_unwound hP env N sub e2 mem2 hsubI hsub
            have hjj := hj K T (N - j)
            rw [show N - j + j = N by omega] at hjj
            have hlim : runLimX env P sub = .unwound e2 mem2 :=
              (runLimX_eq (n := N) (by rw [hsub]; exact fun h => by cases h)).trans hsub
            have hpstep : stepX (linkEnvX P env) (P.only f) xs = resumeUnwind e2 K T mem2 := by
              simp only [stepX, e3, hext, hlim]
              exact raiseIn_eq_resumeUnwind (xs := xs) (c := { t.frame with body := rest }) rs
                e2 mem2 htf htr hts
            have h' := helper _ (N - j) (by omega) hpstep (by rw [hwN, hjj])
            rwa [hwN] at h'
          | trapped c =>
            have hne1 : ∀ vals mem, runLoopX env P N sub ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            have hne2 : ∀ e mem, runLoopX env P N sub ≠ .unwound e mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoopX_below_of_not_ended hP env K T N sub hsubI hne1 hne2, hsub]
            have hlim : runLimX env P sub = .trapped c :=
              (runLimX_eq (n := N) (by rw [hsub]; exact fun h => by cases h)).trans hsub
            refine ⟨1, ?_⟩
            rw [runLoopX_succ']
            simp only [stepX, e3, hext, hlim, e2, hcc, XOutcome.toOutcome, liftStep, afterStepX]
          | stuck msg =>
            have hne1 : ∀ vals mem, runLoopX env P N sub ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            have hne2 : ∀ e mem, runLoopX env P N sub ≠ .unwound e mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoopX_below_of_not_ended hP env K T N sub hsubI hne1 hne2, hsub] at hst
            exact absurd rfl (hst msg)
          | outOfFuel =>
            have hne1 : ∀ vals mem, runLoopX env P N sub ≠ .returned vals mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            have hne2 : ∀ e mem, runLoopX env P N sub ≠ .unwound e mem := by
              rw [hsub]; exact fun _ _ h => by cases h
            rw [runLoopX_below_of_not_ended hP env K T N sub hsubI hne1 hne2, hsub] at hof
            exact absurd rfl hof
  -- the shapes of the step: a `try_call`, or a local step (`lstep`)
  by_cases hT : ∃ fn args et, xs.s.frame.body = [] ∧ xs.s.frame.term = .tryCall fn args et
  · obtain ⟨fn, args, et, hb, ht⟩ := hT
    have e1 := step_try env.toEnv P xs.s hb ht
    have e2 := step_try (linkEnvX P env).toEnv (P.only f) xs.s hb ht
    have r1 : raiseAt? env P xs.s = tryCallRaise env P xs.s.mem xs.s.frame fn args et := by
      simp only [raiseAt?, hb, ht]
    have r2 : raiseAt? (linkEnvX P env) (P.only f) xs.s =
        tryCallRaise (linkEnvX P env) (P.only f) xs.s.mem xs.s.frame fn args et := by
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
        exact call (tryState xs.s bc) [] _ ext vals rfl rfl rfl rfl rfl
          (fun regs => LFrame.jump hI.1.1.1 regs bc) e1 e2 r2 (by rw [← r1]; exact hra)
  · have hnt : ∀ fn args et, xs.s.frame.body = [] → xs.s.frame.term ≠ .tryCall fn args et :=
      fun fn args et hb ht => hT ⟨fn, args, et, hb, ht⟩
    have hci := hI.1.1.headNoCI (hIF _ hI.1.1.1) hnt
    have e1 := Opt.step_eq_lift env.toEnv P xs.s hci
    have e2 := Opt.step_eq_lift (linkEnvX P env).toEnv (P.only f) xs.s hci
    have hlocal : (∀ ext vals rs rest, Opt.lstep xs.s.frame xs.s.mem ≠ .call ext vals rs rest) →
        ∃ m, runLoopX (linkEnvX P env) (P.only f) m xs = runLoopX env P (N + 1) xs := by
      intro hnc
      have r2 : raiseAt? (linkEnvX P env) (P.only f) xs.s = none :=
        raiseAt_none_of_lstep hP hI.1.1 hci hnc
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
      have r2 : raiseAt? (linkEnvX P env) (P.only f) xs.s =
          extRaise (linkEnvX P env) (P.only f) xs.s.mem ext vals := by
        simp only [raiseAt?, hb, hi, callRaise_eq, hca]
      exact call xs.s rest rs ext vals rfl rfl rfl rfl rfl (fun regs => hI.1.1.rest hb regs) e1 e2
        r2 (by rw [← r1]; exact hra)
    | tail ext vals => exact absurd hl (lstep_ne_tail hP hI.1.1)
    | _ => exact hlocal (fun _ _ _ _ h => by rw [hl] at h; cases h)

/-- The initial state of a whole-program run satisfies the invariant. -/
theorem initState_xinv {P : Program} {n : String} {vals : List Val} {mem : Mem} {s : State}
    (h : initState P n vals mem = .ok s) : XInv P s.toX := by
  unfold initState at h
  cases hp : P.func? n with
  | none => simp [hp, Res.ofOption, bind, Res.bind] at h
  | some g =>
    cases he : enterFunc g vals mem with
    | ok a =>
      obtain ⟨fr, mem'⟩ := a
      simp only [hp, he, Res.ofOption, bind, Res.bind, pure, Res.ok.injEq] at h
      subst h
      exact ⟨⟨LFrame.enterFunc (Program.func?_some hp).1 he, fun _ h => by cases h⟩, rfl⟩
    | trap c => simp [hp, he, Res.ofOption, bind, Res.bind] at h
    | stuck m => simp [hp, he, Res.ofOption, bind, Res.bind] at h

/-! ## The exceptions of a run -/

/-- Every extern of `env` that unwinds raises the exception `e0`. -/
def XEnv.RaisesOnly (env : XEnv) (e0 : Exn) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals mem e m, g vals mem = .unwound e m → e = e0

section
variable {env : XEnv} {e0 : Exn} (h0 : env.RaisesOnly e0)
include h0

theorem extern_unwound_only {n : String} {g : List Val → Mem → XOutcome}
    (hg : env.extern n = some g) {vals : List Val} {mem : Mem} {e : Exn} {m : Mem}
    (hr : (match g vals mem with
      | .unwound e m => some (e, m)
      | _ => none : Option (Exn × Mem)) = some (e, m)) : e = e0 := by
  cases hu : g vals mem with
  | unwound e' m' =>
    rw [hu] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact h0 _ g hg _ _ _ _ hu
  | _ => rw [hu] at hr; cases hr

theorem extRaise_only {p : Program} {mem : Mem} {ext : ExtFunc} {vals : List Val} {e : Exn}
    {m : Mem} (hr : extRaise env p mem ext vals = some (e, m)) : e = e0 := by
  unfold extRaise at hr
  cases hp : p.func? ext.name with
  | some _ => rw [hp] at hr; cases hr
  | none =>
    rw [hp] at hr
    cases hg : env.extern ext.name with
    | none => rw [hg] at hr; cases hr
    | some g => rw [hg] at hr; exact extern_unwound_only h0 hg hr

theorem externAtRaise_only {p : Program} {mem : Mem} {d : Signature} {a : Nat}
    {vals : List Val} {e : Exn} {m : Mem}
    (hr : externAtRaise env p mem d a vals = some (e, m)) : e = e0 := by
  unfold externAtRaise at hr
  split at hr
  · rename_i name _
    cases hg : env.extern name with
    | none => rw [hg] at hr; cases hr
    | some g =>
      rw [hg] at hr
      dsimp only at hr
      split at hr
      · exact extern_unwound_only h0 hg hr
      · cases hr
  · cases hr

theorem raiseAt_only {p : Program} {s : State} {e : Exn} {m : Mem}
    (hr : raiseAt? env p s = some (e, m)) : e = e0 := by
  have hcall : ∀ fr fn args, callRaise env p s.mem fr fn args = some (e, m) → e = e0 := by
    intro fr fn args h
    rw [callRaise_eq] at h
    split at h
    · exact extRaise_only h0 h
    · cases h
  have hind : ∀ fr sig callee args, callIndRaise env p s.mem fr sig callee args = some (e, m) →
      e = e0 := by
    intro fr sig callee args h
    unfold callIndRaise at h
    split at h
    · split at h
      · cases h
      · exact externAtRaise_only h0 h
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
            exact extern_unwound_only h0 hg hr
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

end

theorem unwindFrom_unwound_exn (e : Exn) :
    ∀ (fr : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (e' : Exn) (m : Mem), unwindFrom e fr cs ts mem = .unwound e' m → e' = e
  | fr, [], _, mem, e', m, h => by simp only [unwindFrom, XStepResult.unwound.injEq] at h; exact h.1.symm
  | fr, (c, rs) :: cs, t :: ts, mem, e', m, h => by
    simp only [unwindFrom] at h
    split at h
    · rename_i r _
      cases r <;> simp [XStepResult.ofRes] at h
    · exact unwindFrom_unwound_exn e c cs ts _ e' m h
  | fr, _ :: _, [], mem, e', m, h => by simp [unwindFrom] at h

/-- **A run in an environment whose externs raise only `e0` ends by `e0` if it unwinds.** -/
theorem runLoopX_unwound_only {env : XEnv} {e0 : Exn} (h0 : env.RaisesOnly e0) (p : Program) :
    ∀ (N : Nat) (xs : XState) (e : Exn) (m : Mem), runLoopX env p N xs = .unwound e m → e = e0
  | 0, _, _, _, h => by simp [runLoopX] at h
  | N + 1, xs, e, m, h => by
    rw [runLoopX_succ'] at h
    cases hs : stepX env p xs with
    | next xs' => rw [hs] at h; exact runLoopX_unwound_only h0 p N xs' e m h
    | unwound e' m' =>
      rw [hs] at h
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold stepX at hs
      split at hs
      · rename_i e1 mem1 hr
        unfold raiseIn at hs
        split at hs
        · rename_i r _
          cases r <;> simp [XStepResult.ofRes] at hs
        · rw [unwindFrom_unwound_exn _ _ _ _ _ _ _ hs]
          exact raiseAt_only h0 hr
      · cases hstep : step env.toEnv p xs.s <;> rw [hstep] at hs <;> simp [liftStep] at hs
    | _ => rw [hs] at h; cases h

theorem runLimX_unwound_only {env : XEnv} {e0 : Exn} (h0 : env.RaisesOnly e0) (p : Program)
    {xs : XState} {e : Exn} {m : Mem} (h : runLimX env p xs = .unwound e m) : e = e0 := by
  unfold runLimX at h
  split at h
  · exact runLoopX_unwound_only h0 p _ xs e m h
  · cases h

/-! ## Non-vacuity

`Clif.UnwindWitness` (`FV/Clif/Unwind.lean`): `%main` `try_call`s `%mid`, which calls the extern
`%throw`; with tag 7, `throw` unwinds, the exception leaves `%mid` (a plain call) and `%main`'s
`tag7` handler catches it (`caught`: 105). `runLoopX_link` gives the per-function run of
`%main`: the call of `%mid` is atomic, its whole-program run with unwinding ends `unwound`, and
`%main` raises it at its `try_call` — the same result. -/

namespace UnwindLinkWitness

open UnwindWitness

theorem prog_nodup : (prog.funcs.map (·.name)).Nodup := by decide

theorem prog_linkFree : ∀ g ∈ prog.funcs, LinkFree g := by
  intro g hg b hb fn args ht
  simp only [prog, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    simp only [mainFn, midFn, List.mem_cons, List.not_mem_nil, or_false] at hb <;>
    rcases hb with rfl | rfl | rfl | rfl <;> cases ht

theorem prog_indFree : ∀ g ∈ prog.funcs, IndFree g := by
  intro g hg b hb
  simp only [prog, List.mem_cons, List.not_mem_nil, or_false] at hg
  refine ⟨fun st hst sig callee args hi => ?_, fun callee args et ht => ?_⟩ <;>
  rcases hg with rfl | rfl <;>
    simp only [mainFn, midFn, List.mem_cons, List.not_mem_nil, or_false] at hb <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | cases ht
      | (simp only [List.mem_cons, List.not_mem_nil, or_false] at hst <;>
         rcases hst with rfl | rfl <;> cases hi)

/-- **`runLoopX_link` on the witness**: the per-function run of `%main` (a call of `%mid`
atomic, its exception raised at the `try_call`) returns what the whole-program run returns,
105. -/
theorem link_caught : ∃ (xs : XState) (m : Nat),
    (runLoopX (linkEnvX prog (env 7)) (prog.only mainFn) m xs).returnedVals? =
      some [⟨.i64, 105⟩] ∧
    (runLoopX (env 7) prog 20 xs).returnedVals? = some [⟨.i64, 105⟩] := by
  have h := caught
  unfold runX runWithX at h
  cases hm : prog.initMem with
  | ok mem =>
    rw [hm] at h
    dsimp only at h
    cases hi : initState prog "main" [⟨.i64, 5⟩] mem with
    | ok s =>
      rw [hi] at h
      dsimp only at h
      have hr : runLoopX (env 7) prog 20 s.toX ≠ .outOfFuel := by
        intro e; rw [e] at h; cases h
      have hs : ∀ msg, runLoopX (env 7) prog 20 s.toX ≠ .stuck msg := by
        intro msg e; rw [e] at h; cases h
      obtain ⟨m, hm'⟩ := runLoopX_link (f := mainFn) prog_nodup (by simp [prog]) prog_linkFree
        prog_indFree 20 s.toX (initState_xinv hi) hs hr
      exact ⟨s.toX, m, by rw [hm']; exact h, h⟩
    | trap c => rw [hi] at h; simp [XOutcome.returnedVals?] at h
    | stuck msg => rw [hi] at h; simp [XOutcome.returnedVals?] at h
  | trap c => rw [hm] at h; simp [XOutcome.returnedVals?] at h
  | stuck msg => rw [hm] at h; simp [XOutcome.returnedVals?] at h

end UnwindLinkWitness

end Clif
