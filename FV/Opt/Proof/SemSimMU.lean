import FV.Opt.Proof.SemSimMX

/-!
# Memory-aware simulations: raising steps and the program refinement (#1119)

`SemSimU`'s raising steps (`unwindFrom_relU`, `raiseIn_relU`, `sim_raiseU`) and runs
(`sim_stepU`, `runLoopX_refinesU`) for the memory-aware relations of
`FV/Opt/Proof/SemSimMX.lean`. The handler frames a raise resumes are related at the memory the
unwinding left, which has the symbols (`TabRelM`).

* **`runLoopX_refinesSRMU`**: pointwise `FunSimMU` gives the refinement of the runs with
  unwinding from `SRMU`-related states;
* **`runLoopX_refinesMU`**: the same conclusion as `runLoopX_refinesU`, from `SRU`-related states
  (`SRU.toMU`) and pointwise `FunSimMU` (which every pointwise `FunSimU` gives:
  `FunsSimU.toMU`).

Each is the instance of an `…At` statement from pointwise `FunSimMUAt syms`, the simulations at
the run's symbol table only (`runLoopX_refinesMUAt`; `FunsSimMU.at`).
-/

namespace Opt

open Clif

/-! ## Raising steps -/

theorem extRaise_congrMUAt {syms : String → Option Nat} {p q : Program}
    (hP : FunsSimMUAt syms p.funcs q.funcs) (env : XEnv)
    (mem : Mem) (ext : ExtFunc) (vals : List Val) :
    extRaise env q mem ext vals = extRaise env p mem ext vals := by
  obtain ⟨hs, hn⟩ := hP.findP (· == ext.name)
  unfold extRaise
  simp only [Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨g, hq, -⟩ := hs callee hpf
    have hq' : q.funcs.find? (·.name == ext.name) = some g := hq
    rw [hq']
  | none =>
    have hq' : q.funcs.find? (·.name == ext.name) = none := hn hpf
    rw [hq']

theorem indRaise_congrMUAt {syms : String → Option Nat} {p q : Program}
    (hP : FunsSimMUAt syms p.funcs q.funcs) (env : XEnv)
    (mem : Mem) (d : Signature) (a : Nat) (vals : List Val) :
    indRaise env q mem d a vals = indRaise env p mem d a vals := by
  obtain ⟨hs, hn⟩ := hP.findP (fun n => mem.symbols n == some a)
  have hx : q.externNames = p.externNames := hP.externNames
  have hea : externAtRaise env q mem d a vals = externAtRaise env p mem d a vals := by
    unfold externAtRaise; rw [hx]
  unfold indRaise
  rw [hea]
  cases hpf : p.funcs.find? (fun f => mem.symbols f.name == some a) with
  | some t =>
    obtain ⟨t', hq, -⟩ := hs t hpf
    have hq' : q.funcs.find? (fun f => mem.symbols f.name == some a) = some t' := hq
    rw [hq']
  | none =>
    have hq' : q.funcs.find? (fun f => mem.symbols f.name == some a) = none := hn hpf
    rw [hq']

/-- Leaving related frames: the callers' pending tables catch alike, or the run ends with the
same exception and memory. -/
theorem unwindFrom_relMU {syms : String → Option Nat} (e : Exn) :
    ∀ {rtys : List Ty} {fr fr' : Frame} {cs cs' : List (Frame × List ValueId)}
      {ts ts' : List (Option ExnTable)} {m : Mem},
      fr'.slots = fr.slots → m.symbols = syms → CallersRelMU syms rtys cs ts cs' ts' →
      XStepRelMU syms (unwindFrom e fr cs ts m) (unwindFrom e fr' cs' ts' m) := by
  intro rtys fr fr' cs cs' ts ts' m hsl hsym hc
  induction hc generalizing fr fr' m with
  | nil =>
    simp only [unwindFrom, hsl]
    exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h),
      fun _ _ h => h⟩
  | @cons rtys c rs t c' rs' t' cs ts cs' ts' hk hsl' hT hcs ih =>
    simp only [unwindFrom, hsl]
    have hsym' : ((m.free (fr.slots.map (·.2))).leave).symbols = syms := by
      rw [leave_free_symbols]; exact hsym
    obtain ⟨hn, hok⟩ := hT e
    cases hcat : t.bind (catchIn c · e) with
    | none =>
      rw [hn hcat]
      exact ih hsl' hsym'
    | some r =>
      cases r with
      | ok fr1 =>
        obtain ⟨fr1', hcat', hg⟩ := hok fr1 hcat
        rw [hcat']
        simp only [XStepResult.ofRes]
        refine ⟨fun xs1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h),
          fun _ _ h => (by cases h)⟩
        cases h
        obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
        have hf := (catchIn_func hc1).1
        refine ⟨_, rfl, rfl, hsym', hg _ hsym', ?_⟩
        show CallersRelMU syms (AbiParam.tys fr1.func.sig.returns) cs ts cs' ts'
        rw [hf]; exact hcs
      | trap c0 =>
        obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
        exact absurd hc1 (catchIn_ne_trap _ _ _ _)
      | stuck msg =>
        simp only [XStepResult.ofRes]
        exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h),
          fun _ _ h => (by cases h)⟩

/-- Both frames raise `e` with memory `m1` at their calls: their own tables catch alike, else
both frames are left. -/
theorem raiseIn_relMU {syms : String → Option Nat} {s : State} {ts : List (Option ExnTable)}
    {fr2 : Frame} {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)} {e : Exn}
    {m1 : Mem} (hT : TabRelM syms s.frame (pendingOf s) fr2 (pendingOf ⟨fr2, cs', s.mem⟩))
    (hsl : fr2.slots = s.frame.slots) (hsym : m1.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts') :
    XStepRelMU syms (raiseIn ⟨s, ts⟩ e m1) (raiseIn ⟨⟨fr2, cs', s.mem⟩, ts'⟩ e m1) := by
  unfold raiseIn
  simp only
  obtain ⟨hn, hok⟩ := hT e
  cases hcat : (pendingOf s).bind (catchIn s.frame · e) with
  | none =>
    rw [hn hcat]
    exact unwindFrom_relMU e hsl hsym hc
  | some r =>
    cases r with
    | ok fr1 =>
      obtain ⟨fr1', hcat', hg⟩ := hok fr1 hcat
      rw [hcat']
      simp only [XStepResult.ofRes]
      refine ⟨fun xs1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h),
        fun _ _ h => (by cases h)⟩
      cases h
      obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
      have hf := (catchIn_func hc1).1
      refine ⟨_, rfl, rfl, hsym, hg _ hsym, ?_⟩
      show CallersRelMU syms (AbiParam.tys fr1.func.sig.returns) s.callers ts cs' ts'
      rw [hf]; exact hc
    | trap c0 =>
      obtain ⟨et, -, hc1⟩ := bind_catchIn hcat
      exact absurd hc1 (catchIn_ne_trap _ _ _ _)
    | stuck msg =>
      simp only [XStepResult.ofRes]
      exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h),
        fun _ _ h => (by cases h)⟩

/-- **A source step whose callee unwinds**: the target catches up (from the same memory) to the
corresponding call, which raises the same exception with the same memory. -/
theorem sim_raiseMUAt {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimMUAt syms p.funcs q.funcs) {R : Frame → Frame → Mem → Prop}
    (hR : IsSimMU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hr : R s.frame fr' s.mem) (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    {e : Exn} {m1 : Mem} (hra : raiseAt? env p s = some (e, m1)) :
    ∃ s2, Stut env.toEnv q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelMU syms (stepX env p ⟨s, ts⟩) (stepX env q ⟨s2, ts'⟩) := by
  have hS := hR.toIsSimM
  have hsl0 := (hS.frame hr).1
  have hm1 : m1.symbols = syms := (raiseAt_symbols hE hra).trans hsym
  rw [stepX_raise (xs := ⟨s, ts⟩) hra]
  have key : ∀ fr2, LStar fr' s.mem fr2 s.mem →
      raiseAt? env q ⟨fr2, cs', s.mem⟩ = some (e, m1) →
      TabRelM syms s.frame (pendingOf s) fr2 (pendingOf ⟨fr2, cs', s.mem⟩) →
      ∃ s2, Stut env.toEnv q ⟨fr', cs', s.mem⟩ s2 ∧
        XStepRelMU syms (raiseIn ⟨s, ts⟩ e m1) (stepX env q ⟨s2, ts'⟩) := by
    intro fr2 hst hra2 hT
    refine ⟨⟨fr2, cs', s.mem⟩, hst.stut cs', ?_⟩
    rw [stepX_raise (xs := ⟨⟨fr2, cs', s.mem⟩, ts'⟩) hra2]
    exact raiseIn_relMU hT (by rw [(LStar.frame hst).2.1, hsl0]) hm1 hc
  have hra' := hra
  unfold raiseAt? at hra'
  cases hb : s.frame.body with
  | cons st rest =>
    rw [hb] at hra'
    simp only at hra'
    split at hra'
    · rename_i fn args hi
      obtain ⟨ext, vals, hca, hx⟩ := callRaise_inv hra'
      have hl : lstep s.frame s.mem = .call ext vals st.results rest := by
        rw [lstep_call hb hi, hca]; rfl
      obtain ⟨fr2, rs', rest', hst, hl2, -⟩ := hS.call hr hsym hl
      obtain ⟨st', fn', args', hb2, hi2, -, hca2⟩ := lstep_call_inv hl2
      refine key fr2 hst ?_ ?_
      · simp only [raiseAt?, hb2, hi2, callRaise_eq, hca2]
        exact (extRaise_congrMUAt hP env s.mem ext vals).trans hx
      · rw [pendingOf_cons (s := s) hb, pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
        exact TabRelM.none' _ _ _
    · rename_i sig callee args hi
      obtain ⟨d, a, vals, hca, hx⟩ := callIndRaise_inv hra'
      obtain ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2, -⟩ :=
        hR.ci hr hsym hb hi hca
      refine key fr2 hst ?_ ?_
      · simp only [raiseAt?, hb2, hi2, callIndRaise_eq, hca2]
        exact (indRaise_congrMUAt hP env s.mem d a vals).trans hx
      · rw [pendingOf_cons (s := s) hb, pendingOf_cons (s := ⟨fr2, cs', s.mem⟩) hb2]
        exact TabRelM.none' _ _ _
    · cases hra'
  | nil =>
    rw [hb] at hra'
    simp only at hra'
    split at hra'
    · rename_i fn args ht
      obtain ⟨ext, vals, hta, hx⟩ := returnCallRaise_inv hra'
      have hl : lstep s.frame s.mem = .tail ext vals := by
        rw [lstep_term hb, ht]; simp only [hta]; rfl
      obtain ⟨fr2, hst, hl2⟩ := hS.tail hr hsym hl
      obtain ⟨hb2, fn', args', ht2, hta2⟩ := lstep_tail_inv' hl2
      refine key fr2 hst ?_ ?_
      · simp only [raiseAt?, hb2, ht2, returnCallRaise_eq, hta2]
        exact (extRaise_congrMUAt hP env s.mem ext vals).trans hx
      · rw [pendingOf_notTry (s := s) hb (by rw [ht]; rfl),
          pendingOf_notTry (s := ⟨fr2, cs', s.mem⟩) hb2 (by rw [ht2]; rfl)]
        exact TabRelM.none' _ _ _
    · rename_i fn args et ht
      rw [tryCallRaise_eq] at hra'
      split at hra'
      · rename_i x htc
        obtain ⟨n, base, bc⟩ := x
        obtain ⟨ext, vals, hca, hx⟩ := callRaise_inv hra'
        obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, -, hh⟩ :=
          hR.tc.call hr hsym hb ht htc hca
        refine key fr2 hst ?_ ?_
        · simp only [raiseAt?, hb2, ht2, tryCallRaise_eq, htc2, callRaise_eq, hca2]
          exact (extRaise_congrMUAt hP env s.mem ext vals).trans hx
        · rw [pendingOf_try (s := s) hb ht, pendingOf_try (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
          exact TabRelM.ofH hR hh
      · cases hra'
    · rename_i callee args et ht
      rw [tryCallIndRaise_eq] at hra'
      split at hra'
      · rename_i x htc
        obtain ⟨n, base, bc⟩ := x
        obtain ⟨d, a, vals, hca, hx⟩ := callIndRaise_inv hra'
        obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, -, hh⟩ :=
          hR.tc.ind hr hsym hb ht htc hca
        refine key fr2 hst ?_ ?_
        · simp only [raiseAt?, hb2, ht2, tryCallIndRaise_eq, htc2, callIndRaise_eq, hca2]
          exact (indRaise_congrMUAt hP env s.mem d a vals).trans hx
        · rw [pendingOf_tryInd (s := s) hb ht,
            pendingOf_tryInd (s := ⟨fr2, cs', s.mem⟩) hb2 ht2]
          exact TabRelM.ofH hR hh
      · cases hra'
    · cases hra'

/-! ## Runs -/

/-- A related target step is the target's step with unwinding where the source step is not
`stuck`. -/
theorem XStepRelMU.toStepX {syms : String → Option Nat} {env : XEnv} {q : Program}
    {r : XStepResult} {s2 : State} {ts' : List (Option ExnTable)} {n : Nat}
    (h : XStepRelMU syms r (liftWith n (pendingOf s2) ts' (step env.toEnv q s2)))
    (hn : s2.callers.length = n) : XStepRelMU syms r (stepX env q ⟨s2, ts'⟩) := by
  subst hn
  have key : ∀ r', liftWith s2.callers.length (pendingOf s2) ts' (step env.toEnv q s2) = r' →
      (∀ m, r' ≠ .stuck m) → stepX env q ⟨s2, ts'⟩ = r' := by
    intro r' h1 h2
    have hns : ∀ msg, step env.toEnv q s2 ≠ .stuck msg := by
      intro msg hm; rw [hm] at h1; exact h2 msg h1.symm
    rw [stepX_of_not_stuck (xs := ⟨s2, ts'⟩) hns, liftStep_eq]
    exact h1
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun xs1 hx => ?_, fun vs m hx => ?_, fun c hx => ?_, fun e m hx => ?_⟩
  · obtain ⟨xs1', he, hr⟩ := h1 xs1 hx
    exact ⟨xs1', key _ he (fun _ h => by cases h), hr⟩
  · exact key _ (h2 vs m hx) (fun _ h => by cases h)
  · exact key _ (h3 c hx) (fun _ h => by cases h)
  · exact key _ (h4 e m hx) (fun _ h => by cases h)

/-- **One source step with unwinding** (`sim_stepU` with the memory): matched by target
stuttering steps, or by target stuttering steps followed by one related step. -/
theorem sim_stepMUAt {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimMUAt syms p.funcs q.funcs) {xs xs' : XState}
    (h : SRMU syms xs xs') :
    (∃ xs1 s1', stepX env p xs = .next xs1 ∧ Stut env.toEnv q xs'.s s1' ∧
      SRMU syms xs1 ⟨s1', xs'.tries⟩) ∨
    (∃ s2, Stut env.toEnv q xs'.s s2 ∧
      XStepRelMU syms (stepX env p xs) (stepX env q ⟨s2, xs'.tries⟩)) := by
  obtain ⟨s, ts⟩ := xs
  obtain ⟨⟨fr', cs', m'⟩, ts'⟩ := xs'
  obtain ⟨hm, hsym, ⟨R, hR, hfr⟩, hc⟩ := h
  simp only at hm hsym hfr hc
  subst hm
  cases hra : raiseAt? env p s with
  | some em =>
    obtain ⟨e, m1⟩ := em
    right
    rcases hfr with hr | ⟨hb, -, bc, -, ht, -, -⟩
    · exact sim_raiseMUAt hE hP hR hr hsym hc hra
    · rw [raiseAt_jump hb ht] at hra; cases hra
  | none =>
    have hstep := stepX_none (xs := ⟨s, ts⟩) hra
    rcases sim_stepMU_coreAt hE.toEnv hP hR hfr hsym hc with
      ⟨s1, s1', hs1, hstut, hcl, hrel⟩ | ⟨s2, hstut, hrel⟩
    · left
      refine ⟨⟨s1, ts⟩, s1', ?_, hstut, hrel⟩
      rw [hstep, liftStep_eq]
      simp only [hs1]
      exact liftWith_same (by rw [hcl])
    · right
      refine ⟨s2, hstut, ?_⟩
      rw [hstep, liftStep_eq]
      exact hrel.toStepX (by rw [hstut.callers]; exact hc.length)

/-- **Program refinement with unwinding, memory-aware simulations at the run's symbol table.**
If every function of `p` is simulated with its handler edges, at the symbol table `syms`, by a
memory-aware simulation (`FunSimMUAt syms`) by the corresponding function of `q`,
`SRMU syms`-related states have related runs with unwinding: a source run that returns, traps or
ends `unwound e m` within `n` steps is matched by a target run of some length with the same
outcome. -/
theorem runLoopX_refinesSRMUAt {syms : String → Option Nat} {env : XEnv}
    (hE : EnvKeepsSymbolsX env) {p q : Program} (hP : FunsSimMUAt syms p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRMU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') := by
  intro n
  induction n with
  | zero =>
    intro xs xs' _
    exact ⟨0, fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
  | succ n ih =>
    intro xs xs' h
    obtain ⟨s', ts'⟩ := xs'
    rcases sim_stepMUAt hE hP h with ⟨xs1, s1', hst, hstut, hr⟩ | ⟨s2, hstut, hr⟩
    · obtain ⟨n1, hn1⟩ := ih xs1 _ hr
      obtain ⟨k, hk⟩ := hstut.runLoopX ts'
      refine ⟨n1 + k, ?_⟩
      rw [hk, runLoopX_of_next hst]
      exact hn1
    · obtain ⟨hn, hd, ht, hu⟩ := hr
      obtain ⟨k, hk⟩ := hstut.runLoopX ts'
      rw [Clif.runLoopX]
      cases hs : stepX env p xs with
      | next xs1 =>
        obtain ⟨xs1', hs', hr'⟩ := hn xs1 hs
        obtain ⟨n1, hn1⟩ := ih _ _ hr'
        refine ⟨n1 + 1 + k, ?_⟩
        rw [hk, runLoopX_of_next hs']
        exact hn1
      | done vs m =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, Clif.runLoopX, hd vs m hs]
        exact ⟨fun _ _ h => h, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩
      | trapped c =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, Clif.runLoopX, ht c hs]
        exact ⟨fun _ _ h => (by cases h), fun _ h => h, fun _ _ h => (by cases h)⟩
      | unwound e m =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, Clif.runLoopX, hu e m hs]
        exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => h⟩
      | stuck m =>
        exact ⟨0, fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- **Program refinement with unwinding at one symbol table**: the conclusion of
`runLoopX_refinesU` for runs at `syms`, from pointwise `FunSimMUAt syms`. -/
theorem runLoopX_refinesMUAt {syms : String → Option Nat} {env : XEnv}
    (hE : EnvKeepsSymbolsX env) {p q : Program} (hP : FunsSimMUAt syms p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  fun n xs xs' h => runLoopX_refinesSRMUAt hE hP n xs xs' h.toMU

/-! ## The statements for pointwise `FunSimMU` (every symbol table) -/

theorem extRaise_congrMU {p q : Program} (hP : FunsSimMU p.funcs q.funcs) (env : XEnv)
    (mem : Mem) (ext : ExtFunc) (vals : List Val) :
    extRaise env q mem ext vals = extRaise env p mem ext vals :=
  extRaise_congrMUAt (hP.at mem.symbols) env mem ext vals

theorem indRaise_congrMU {p q : Program} (hP : FunsSimMU p.funcs q.funcs) (env : XEnv)
    (mem : Mem) (d : Signature) (a : Nat) (vals : List Val) :
    indRaise env q mem d a vals = indRaise env p mem d a vals :=
  indRaise_congrMUAt (hP.at mem.symbols) env mem d a vals

/-- **A source step whose callee unwinds**: the target catches up (from the same memory) to the
corresponding call, which raises the same exception with the same memory. -/
theorem sim_raiseMU {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {R : Frame → Frame → Mem → Prop}
    (hR : IsSimMU syms R) {s : State} {ts : List (Option ExnTable)} {fr' : Frame}
    {cs' : List (Frame × List ValueId)} {ts' : List (Option ExnTable)}
    (hr : R s.frame fr' s.mem) (hsym : s.mem.symbols = syms)
    (hc : CallersRelMU syms (AbiParam.tys s.frame.func.sig.returns) s.callers ts cs' ts')
    {e : Exn} {m1 : Mem} (hra : raiseAt? env p s = some (e, m1)) :
    ∃ s2, Stut env.toEnv q ⟨fr', cs', s.mem⟩ s2 ∧
      XStepRelMU syms (stepX env p ⟨s, ts⟩) (stepX env q ⟨s2, ts'⟩) :=
  sim_raiseMUAt hE (hP.at syms) hR hr hsym hc hra

/-- **One source step with unwinding** (`sim_stepU` with the memory): matched by target
stuttering steps, or by target stuttering steps followed by one related step. -/
theorem sim_stepMU {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) {xs xs' : XState} (h : SRMU syms xs xs') :
    (∃ xs1 s1', stepX env p xs = .next xs1 ∧ Stut env.toEnv q xs'.s s1' ∧
      SRMU syms xs1 ⟨s1', xs'.tries⟩) ∨
    (∃ s2, Stut env.toEnv q xs'.s s2 ∧
      XStepRelMU syms (stepX env p xs) (stepX env q ⟨s2, xs'.tries⟩)) :=
  sim_stepMUAt hE (hP.at syms) h

/-- **Program refinement with unwinding, memory-aware simulations.** If every function of `p` is
simulated with its handler edges by a memory-aware simulation (`FunSimMU`) by the corresponding
function of `q`, `SRMU`-related states have related runs with unwinding: a source run that
returns, traps or ends `unwound e m` within `n` steps is matched by a target run of some length
with the same outcome. -/
theorem runLoopX_refinesSRMU {syms : String → Option Nat} {env : XEnv}
    (hE : EnvKeepsSymbolsX env) {p q : Program} (hP : FunsSimMU p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRMU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  runLoopX_refinesSRMUAt hE (hP.at syms)

/-- **Program refinement with unwinding from memory-aware function simulations**: exactly the
conclusion of `runLoopX_refinesU`, from pointwise `FunSimMU`. -/
theorem runLoopX_refinesMU {syms : String → Option Nat} {env : XEnv} (hE : EnvKeepsSymbolsX env)
    {p q : Program} (hP : FunsSimMU p.funcs q.funcs) :
    ∀ n (xs xs' : XState), SRU syms xs xs' →
      ∃ n', XOutcomeRefines (Clif.runLoopX env p n xs) (Clif.runLoopX env q n' xs') :=
  fun n xs xs' h => runLoopX_refinesSRMU hE hP n xs xs' h.toMU

end Opt
