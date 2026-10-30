import FV.E2E.LinkPlace
import FV.E2E.UnwindStatement
import FV.Clif.LinkClifXN

/-!
# The CLIF runs with unwinding of a linked program: the memory facts (S10f, #233)

`FV/E2E/LinkPlace.lean`'s facts on returning whole-program runs, for the runs with unwinding
(`Clif.runLoopX`): an exception propagating out of frames frees their slots and pops their stack
pointers off the slot-placement oracle (`unwindFrom`), as a return does.

* `XEnvKeepsPlace`/`XEnvKeepsAllocs`: externs that keep the oracle / create no allocation, also
  when they unwind.
* `runLoopX_place`, `runLoopX_placeNone`: a returning or unwinding whole-program run gives back
  the oracle of its entry; `linkEnvRX_keepsPlace0`: so the linked environment keeps the oracle
  (on memories without the slot-byte oracle).
* `runLoopX_allocs`: a returning or unwinding whole-program run creates no allocation.
* `trapsExplicitX_of_returned`/`_of_unwound`: a returning or unwinding run of a program without
  functions satisfies the run premises `TrapsExplicitX`.
-/

namespace Clif

open E2E Opt

/-- The externs keep the slot-placement oracle, also when they unwind. -/
def XEnvKeepsPlace (env : XEnv) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m,
    (∀ rvals m', g vals m = .returned rvals m' → m'.place = m.place) ∧
    (∀ e m', g vals m = .unwound e m' → m'.place = m.place)

/-- The externs create no allocation, also when they unwind. -/
def XEnvKeepsAllocs (env : XEnv) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m,
    (∀ rvals m', g vals m = .returned rvals m' → ∀ x ∈ m'.allocs, x ∈ m.allocs) ∧
    (∀ e m', g vals m = .unwound e m' → ∀ x ∈ m'.allocs, x ∈ m.allocs)

theorem toOutcome_returned {o : XOutcome} {v : List Val} {m : Mem}
    (h : o.toOutcome = .returned v m) : o = .returned v m := by
  cases o <;> simp_all [XOutcome.toOutcome]

theorem XEnvKeepsPlace.toEnv {env : XEnv} (h : XEnvKeepsPlace env) :
    EnvKeepsPlace env.toEnv := by
  intro n g hg vals m rvals m' hr
  simp only [XEnv.toEnv, Option.map_eq_some_iff] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  exact (h n g0 hg0 vals m).1 rvals m' (toOutcome_returned hr)

/-- `XEnvKeepsPlace` on the memories without the slot-byte oracle (`Place.init = none`): what a
linked environment keeps (`linkEnvRX_keepsPlace0`), whose program callees advance the slot-byte
oracle. -/
def XEnvKeepsPlace0 (env : XEnv) : Prop :=
  ∀ n g, env.extern n = some g → ∀ vals m, (∀ pl, m.place = some pl → pl.init = none) →
    (∀ rvals m', g vals m = .returned rvals m' → m'.place = m.place) ∧
    (∀ e m', g vals m = .unwound e m' → m'.place = m.place)

theorem XEnvKeepsPlace0.toEnv {env : XEnv} (h : XEnvKeepsPlace0 env) :
    EnvKeepsPlace0 env.toEnv := by
  intro n g hg vals m rvals m' hm0 hr
  simp only [XEnv.toEnv, Option.map_eq_some_iff] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  exact (h n g0 hg0 vals m hm0).1 rvals m' (toOutcome_returned hr)

theorem XEnvKeepsAllocs.toEnv {env : XEnv} (h : XEnvKeepsAllocs env) :
    EnvKeepsAllocs env.toEnv := by
  intro n g hg vals m rvals m' hr
  simp only [XEnv.toEnv, Option.map_eq_some_iff] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  exact (h n g0 hg0 vals m).1 rvals m' (toOutcome_returned hr)

/-- An environment with unwinding whose externs never unwind and whose `Clif.run` externs keep
the oracle (create no allocation) does so with unwinding. -/
theorem xEnvKeepsPlace_of {env : XEnv} (hr : EnvKeepsPlace env.toEnv)
    (hu : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
      m'.place = m.place) : XEnvKeepsPlace env := by
  intro n g hg vals m
  refine ⟨fun rvals m' h => hr n (fun vals mem => (g vals mem).toOutcome)
    (by simp [XEnv.toEnv, hg]) vals m rvals m' (by simp [h, XOutcome.toOutcome]),
    fun e m' h => hu n g hg vals m e m' h⟩

theorem xEnvKeepsAllocs_of {env : XEnv} (hr : EnvKeepsAllocs env.toEnv)
    (hu : ∀ n g, env.extern n = some g → ∀ vals m e m', g vals m = .unwound e m' →
      ∀ x ∈ m'.allocs, x ∈ m.allocs) : XEnvKeepsAllocs env := by
  intro n g hg vals m
  refine ⟨fun rvals m' h => hr n (fun vals mem => (g vals mem).toOutcome)
    (by simp [XEnv.toEnv, hg]) vals m rvals m' (by simp [h, XOutcome.toOutcome]),
    fun e m' h => hu n g hg vals m e m' h⟩

/-! ## The slot-placement oracle -/

theorem leave_free_place {mem : Mem} {bs : List Nat} {pl : Place} (h : mem.place = some pl) :
    ((mem.free bs).leave).place = some { pl with sps := pl.sps.tail } := by
  simp only [Mem.leave, Mem.free, h]

theorem leave_free_placeNone {mem : Mem} {bs : List Nat} (h : mem.place = none) :
    ((mem.free bs).leave).place = none := by
  simp only [Mem.leave, Mem.free, h]

/-- **An exception propagating out of frames pops their stack pointers off the oracle** (with
any slot-byte oracle `i`, which it keeps). -/
theorem unwindFrom_placeI (e : Exn) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} {i : Option SlotInit} :
    ∀ (f : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (l : List (BitVec 64)), mem.place = some ⟨l ++ sps, fr, i⟩ → l.length = cs.length + 1 →
      (∀ xs', unwindFrom e f cs ts mem = .next xs' →
        ∃ l', xs'.s.mem.place = some ⟨l' ++ sps, fr, i⟩ ∧ l'.length = xs'.s.callers.length + 1) ∧
      (∀ e' m', unwindFrom e f cs ts mem = .unwound e' m' → m'.place = some ⟨sps, fr, i⟩)
  | f, [], _, mem, l, hp, hl => by
    refine ⟨fun xs' h => by simp [unwindFrom] at h, fun e' m' h => ?_⟩
    simp only [unwindFrom, XStepResult.unwound.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [leave_free_place hp]
    cases l with
    | nil => simp at hl
    | cons y l' =>
      cases l' with
      | nil => rfl
      | cons => simp at hl
  | f, (c, rs) :: cs, t :: ts, mem, l, hp, hl => by
    have hp1 : ((mem.free (f.slots.map (·.2))).leave).place = some ⟨l.tail ++ sps, fr, i⟩ := by
      rw [leave_free_place hp]
      cases l with
      | nil => simp at hl
      | cons y l' => rfl
    have hl1 : l.tail.length = cs.length + 1 := by
      cases l with
      | nil => simp at hl
      | cons y l' => simpa using hl
    have ih := unwindFrom_placeI e c cs ts _ l.tail hp1 hl1
    simp only [unwindFrom]
    split
    · rename_i r _
      cases r with
      | ok fr' =>
        refine ⟨fun xs' h => ?_, fun e' m' h => by simp [XStepResult.ofRes] at h⟩
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        exact ⟨l.tail, hp1, hl1⟩
      | trap c => exact ⟨fun _ h => by simp [XStepResult.ofRes] at h,
          fun _ _ h => by simp [XStepResult.ofRes] at h⟩
      | stuck m => exact ⟨fun _ h => by simp [XStepResult.ofRes] at h,
          fun _ _ h => by simp [XStepResult.ofRes] at h⟩
    · exact ih
  | f, _ :: _, [], mem, l, hp, hl => by
    exact ⟨fun _ h => by simp [unwindFrom] at h, fun _ _ h => by simp [unwindFrom] at h⟩

/-- **An exception propagating out of frames pops their stack pointers off the oracle.** -/
theorem unwindFrom_place (e : Exn) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} :
    ∀ (f : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem)
      (l : List (BitVec 64)), mem.place = some ⟨l ++ sps, fr, none⟩ → l.length = cs.length + 1 →
      (∀ xs', unwindFrom e f cs ts mem = .next xs' →
        ∃ l', xs'.s.mem.place = some ⟨l' ++ sps, fr, none⟩ ∧ l'.length = xs'.s.callers.length + 1) ∧
      (∀ e' m', unwindFrom e f cs ts mem = .unwound e' m' → m'.place = some ⟨sps, fr, none⟩) :=
  unwindFrom_placeI e

/-- Without an oracle propagating an exception keeps none. -/
theorem unwindFrom_placeNone (e : Exn) :
    ∀ (f : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem),
      mem.place = none →
      (∀ xs', unwindFrom e f cs ts mem = .next xs' → xs'.s.mem.place = none) ∧
      (∀ e' m', unwindFrom e f cs ts mem = .unwound e' m' → m'.place = none)
  | f, [], _, mem, hp => by
    refine ⟨fun xs' h => by simp [unwindFrom] at h, fun e' m' h => ?_⟩
    simp only [unwindFrom, XStepResult.unwound.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact leave_free_placeNone hp
  | f, (c, rs) :: cs, t :: ts, mem, hp => by
    have hp1 := leave_free_placeNone (bs := f.slots.map (·.2)) hp
    have ih := unwindFrom_placeNone e c cs ts _ hp1
    simp only [unwindFrom]
    split
    · rename_i r _
      cases r with
      | ok fr' =>
        refine ⟨fun xs' h => ?_, fun e' m' h => by simp [XStepResult.ofRes] at h⟩
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        exact hp1
      | trap c => exact ⟨fun _ h => by simp [XStepResult.ofRes] at h,
          fun _ _ h => by simp [XStepResult.ofRes] at h⟩
      | stuck m => exact ⟨fun _ h => by simp [XStepResult.ofRes] at h,
          fun _ _ h => by simp [XStepResult.ofRes] at h⟩
    · exact ih
  | f, _ :: _, [], mem, _ => by
    exact ⟨fun _ h => by simp [unwindFrom] at h, fun _ _ h => by simp [unwindFrom] at h⟩

/-- The exception caught by the raising frame itself: the frame at its handler, the extern's
memory, the same callers and tables. -/
theorem raiseIn_cases {xs xs' : XState} {e : Exn} {mem : Mem} (h : raiseIn xs e mem = .next xs') :
    (∃ fr, xs' = ⟨{ xs.s with frame := fr, mem }, xs.tries⟩ ∧ fr.slots = xs.s.frame.slots) ∨
      unwindFrom e xs.s.frame xs.s.callers xs.tries mem = .next xs' := by
  unfold raiseIn at h
  split at h
  · rename_i r hr
    cases r with
    | ok fr =>
      simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
      obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
      exact .inl ⟨_, h.symm, rfl⟩
    | trap c => simp [XStepResult.ofRes] at h
    | stuck m => simp [XStepResult.ofRes] at h
  · exact .inr h

theorem raiseIn_unwound {xs : XState} {e e' : Exn} {mem m' : Mem}
    (h : raiseIn xs e mem = .unwound e' m') :
    unwindFrom e xs.s.frame xs.s.callers xs.tries mem = .unwound e' m' := by
  unfold raiseIn at h
  split at h
  · rename_i r _
    cases r <;> simp [XStepResult.ofRes] at h
  · exact h

theorem raiseIn_ne_done {xs : XState} {e : Exn} {mem : Mem} {v : List Val} {m : Mem} :
    raiseIn xs e mem ≠ .done v m := by
  intro h
  unfold raiseIn at h
  split at h
  · rename_i r _
    cases r <;> simp [XStepResult.ofRes] at h
  · exact unwindFrom_ne_done e _ _ _ _ v m h

/-- **A whole-program step with unwinding keeps the oracle invariant** (when the externs keep
the oracle). -/
theorem placeInvX_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : XEnvKeepsPlace env) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} {xs : XState} (hI : XInv P xs)
    (hp : PlaceInv sps fr xs.s) :
    (∀ xs', stepX env P xs = .next xs' → PlaceInv sps fr xs'.s) ∧
    (∀ v m, stepX env P xs = .done v m → m.place = some ⟨sps, fr, none⟩) ∧
    (∀ e m, stepX env P xs = .unwound e m → m.place = some ⟨sps, fr, none⟩) := by
  obtain ⟨l, hl, hlen⟩ := hp
  unfold stepX
  split
  · rename_i e mem hr
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hr
    have hm : mem.place = some ⟨l ++ sps, fr, none⟩ := by rw [(hk n g hg vals _).2 e mem hu, hl]
    have hU := unwindFrom_place e xs.s.frame xs.s.callers xs.tries mem l hm hlen
    refine ⟨fun xs' h => ?_, fun v m h => absurd h raiseIn_ne_done,
      fun e' m' h => hU.2 e' m' (raiseIn_unwound h)⟩
    rcases raiseIn_cases h with ⟨fr', rfl, -⟩ | h
    · exact ⟨l, hm, hlen⟩
    · exact hU.1 xs' h
  · have hs := placeInv_step hP hk.toEnv hI.1 ⟨l, hl, hlen⟩
    refine ⟨fun xs' h => ?_, fun v m h => ?_, fun e m h => ?_⟩
    · cases hst : step env.toEnv P xs.s with
      | next s1 =>
        rw [hst] at h
        simp only [liftStep, XStepResult.next.injEq] at h
        subst h
        exact hs.1 s1 hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s with
      | done v' m' =>
        rw [hst] at h
        simp only [liftStep, XStepResult.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hs.2 _ _ hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s <;> rw [hst] at h <;> simp [liftStep] at h

theorem placeNoneX_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : XEnvKeepsPlace env) {xs : XState} (hI : XInv P xs) (hp : xs.s.mem.place = none) :
    (∀ xs', stepX env P xs = .next xs' → xs'.s.mem.place = none) ∧
    (∀ v m, stepX env P xs = .done v m → m.place = none) ∧
    (∀ e m, stepX env P xs = .unwound e m → m.place = none) := by
  unfold stepX
  split
  · rename_i e mem hr
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hr
    have hm : mem.place = none := by rw [(hk n g hg vals _).2 e mem hu, hp]
    have hU := unwindFrom_placeNone e xs.s.frame xs.s.callers xs.tries mem hm
    refine ⟨fun xs' h => ?_, fun v m h => absurd h raiseIn_ne_done,
      fun e' m' h => hU.2 e' m' (raiseIn_unwound h)⟩
    rcases raiseIn_cases h with ⟨fr', rfl, -⟩ | h
    · exact hm
    · exact hU.1 xs' h
  · have hs := placeNone_step hP hk.toEnv hI.1 hp
    refine ⟨fun xs' h => ?_, fun v m h => ?_, fun e m h => ?_⟩
    · cases hst : step env.toEnv P xs.s with
      | next s1 =>
        rw [hst] at h
        simp only [liftStep, XStepResult.next.injEq] at h
        subst h
        exact hs.1 s1 hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s with
      | done v' m' =>
        rw [hst] at h
        simp only [liftStep, XStepResult.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hs.2 _ _ hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s <;> rw [hst] at h <;> simp [liftStep] at h

/-- **A returning or unwinding whole-program run with unwinding gives back the oracle.** -/
theorem runLoopX_place {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : XEnvKeepsPlace env) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} :
    ∀ (N : Nat) (xs : XState), XInv P xs → PlaceInv sps fr xs.s →
      (∀ vals mem, runLoopX env P N xs = .returned vals mem → mem.place = some ⟨sps, fr, none⟩) ∧
      (∀ e mem, runLoopX env P N xs = .unwound e mem → mem.place = some ⟨sps, fr, none⟩)
  | 0, _, _, _ => ⟨fun _ _ h => by simp [runLoopX] at h, fun _ _ h => by simp [runLoopX] at h⟩
  | N + 1, xs, hI, hp => by
    have hs := placeInvX_step hP hk hI hp
    rw [runLoopX_succ']
    cases hst : stepX env P xs with
    | next xs' =>
      exact runLoopX_place hP hk N xs' (stepX_next_xinv hP hI hst) (hs.1 xs' hst)
    | done v m =>
      refine ⟨fun vals mem h => ?_, fun e mem h => by simp [afterStepX] at h⟩
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.1 _ _ hst
    | unwound e m =>
      refine ⟨fun vals mem h => by simp [afterStepX] at h, fun e' mem h => ?_⟩
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.2 _ _ hst
    | trapped c => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩
    | stuck m => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩

theorem runLoopX_placeNone {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : XEnvKeepsPlace env) :
    ∀ (N : Nat) (xs : XState), XInv P xs → xs.s.mem.place = none →
      (∀ vals mem, runLoopX env P N xs = .returned vals mem → mem.place = none) ∧
      (∀ e mem, runLoopX env P N xs = .unwound e mem → mem.place = none)
  | 0, _, _, _ => ⟨fun _ _ h => by simp [runLoopX] at h, fun _ _ h => by simp [runLoopX] at h⟩
  | N + 1, xs, hI, hp => by
    have hs := placeNoneX_step hP hk hI hp
    rw [runLoopX_succ']
    cases hst : stepX env P xs with
    | next xs' =>
      exact runLoopX_placeNone hP hk N xs' (stepX_next_xinv hP hI hst) (hs.1 xs' hst)
    | done v m =>
      refine ⟨fun vals mem h => ?_, fun e mem h => by simp [afterStepX] at h⟩
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.1 _ _ hst
    | unwound e m =>
      refine ⟨fun vals mem h => by simp [afterStepX] at h, fun e' mem h => ?_⟩
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.2 _ _ hst
    | trapped c => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩
    | stuck m => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩

theorem initState_placeNone {P : Program} {n : String} {vals : List Val} {m : Mem} {s : State}
    (hi : initState P n vals m = .ok s) (hm : m.place = none) : s.mem.place = none := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at hi
  obtain ⟨g, -, ⟨fr, mem'⟩, he, rfl⟩ := hi
  obtain ⟨_, _, _, _, _, _, hal, -⟩ := Opt.enterFunc_ok he
  have := (enterSlots_place_init g m).1 hm
  rwa [hal] at this

/-- **The linked environment with unwinding keeps the oracle** without the slot-byte oracle (the
program's functions' runs give it back, also when they unwind) when the base externs keep it. -/
theorem linkEnvRX_keepsPlace0 {P : Program} {env : XEnv} {R : State → XOutcome}
    (hR : ∀ s o, R s = o → ((∃ vals mem, o = .returned vals mem) ∨ ∃ e mem, o = .unwound e mem) →
      ∃ N, runLoopX env P N s.toX = o)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hk : XEnvKeepsPlace env) :
    XEnvKeepsPlace0 (linkEnvRX P env R) := by
  intro n gsem hg vals m hm0
  cases hpf : P.func? n with
  | none => rw [linkEnvRX_none hpf] at hg; exact hk n gsem hg vals m
  | some g =>
    rw [linkEnvRX_some hpf] at hg
    cases hg
    cases hi : initState P n vals m with
    | ok s =>
      have hI := initState_xinv hi
      have key : ∀ o, R s = o → ((∃ vals mem, o = .returned vals mem) ∨
          ∃ e mem, o = .unwound e mem) →
          (∀ vals mem, o = .returned vals mem → mem.place = m.place) ∧
          (∀ e mem, o = .unwound e mem → mem.place = m.place) := by
        intro o ho hc
        obtain ⟨N, hN⟩ := hR s o ho hc
        cases hmp : m.place with
        | none =>
          have := runLoopX_placeNone hP hk N s.toX hI (initState_placeNone hi hmp)
          exact ⟨fun v mem h => this.1 v mem (h ▸ hN), fun e mem h => this.2 e mem (h ▸ hN)⟩
        | some pl =>
          obtain ⟨sps, frm, i⟩ := pl
          have hi0 : i = none := hm0 _ hmp
          subst hi0
          have := runLoopX_place hP hk N s.toX hI (initState_place hi hmp rfl)
          exact ⟨fun v mem h => this.1 v mem (h ▸ hN), fun e mem h => this.2 e mem (h ▸ hN)⟩
      refine ⟨fun rvals m' h => ?_, fun e m' h => ?_⟩
      · simp only [hi] at h
        exact (key _ h (.inl ⟨_, _, rfl⟩)).1 _ _ rfl
      · simp only [hi] at h
        exact (key _ h (.inr ⟨_, _, rfl⟩)).2 _ _ rfl
    | trap c => exact ⟨fun _ _ h => by simp [hi] at h, fun _ _ h => by simp [hi] at h⟩
    | stuck msg => exact ⟨fun _ _ h => by simp [hi] at h, fun _ _ h => by simp [hi] at h⟩

/-! ## Slotless programs keep any slot-byte oracle (with unwinding) -/

theorem placeInvXI_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hS : ∀ g ∈ P.funcs, g.slots = []) {env : XEnv}
    (hk : XEnvKeepsPlace env) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} {i : Option SlotInit} {xs : XState}
    (hI : XInv P xs) (hp : PlaceInvI sps fr i xs.s) :
    (∀ xs', stepX env P xs = .next xs' → PlaceInvI sps fr i xs'.s) ∧
    (∀ v m, stepX env P xs = .done v m → m.place = some ⟨sps, fr, i⟩) ∧
    (∀ e m, stepX env P xs = .unwound e m → m.place = some ⟨sps, fr, i⟩) := by
  obtain ⟨l, hl, hlen⟩ := hp
  unfold stepX
  split
  · rename_i e mem hr
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hr
    have hm : mem.place = some ⟨l ++ sps, fr, i⟩ := by rw [(hk n g hg vals _).2 e mem hu, hl]
    have hU := unwindFrom_placeI e xs.s.frame xs.s.callers xs.tries mem l hm hlen
    refine ⟨fun xs' h => ?_, fun v m h => absurd h raiseIn_ne_done,
      fun e' m' h => hU.2 e' m' (raiseIn_unwound h)⟩
    rcases raiseIn_cases h with ⟨fr', rfl, -⟩ | h
    · exact ⟨l, hm, hlen⟩
    · exact hU.1 xs' h
  · have hs := placeInvI_step hP hS hk.toEnv hI.1 ⟨l, hl, hlen⟩
    refine ⟨fun xs' h => ?_, fun v m h => ?_, fun e m h => ?_⟩
    · cases hst : step env.toEnv P xs.s with
      | next s1 =>
        rw [hst] at h
        simp only [liftStep, XStepResult.next.injEq] at h
        subst h
        exact hs.1 s1 hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s with
      | done v' m' =>
        rw [hst] at h
        simp only [liftStep, XStepResult.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hs.2 _ _ hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s <;> rw [hst] at h <;> simp [liftStep] at h

theorem runLoopX_placeI {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g)
    (hS : ∀ g ∈ P.funcs, g.slots = []) {env : XEnv}
    (hk : XEnvKeepsPlace env) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} {i : Option SlotInit} :
    ∀ (N : Nat) (xs : XState), XInv P xs → PlaceInvI sps fr i xs.s →
      (∀ vals mem, runLoopX env P N xs = .returned vals mem → mem.place = some ⟨sps, fr, i⟩) ∧
      (∀ e mem, runLoopX env P N xs = .unwound e mem → mem.place = some ⟨sps, fr, i⟩)
  | 0, _, _, _ => ⟨fun _ _ h => by simp [runLoopX] at h, fun _ _ h => by simp [runLoopX] at h⟩
  | N + 1, xs, hI, hp => by
    have hs := placeInvXI_step hP hS hk hI hp
    rw [runLoopX_succ']
    cases hst : stepX env P xs with
    | next xs' =>
      exact runLoopX_placeI hP hS hk N xs' (stepX_next_xinv hP hI hst) (hs.1 xs' hst)
    | done v m =>
      refine ⟨fun vals mem h => ?_, fun e mem h => by simp [afterStepX] at h⟩
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.1 _ _ hst
    | unwound e m =>
      refine ⟨fun vals mem h => by simp [afterStepX] at h, fun e' mem h => ?_⟩
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.2 _ _ hst
    | trapped c => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩
    | stuck m => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩

/-- **The linked environment with unwinding of a slotless program keeps the oracle** (slot-byte
oracle included) when the base externs keep it. -/
theorem linkEnvRX_keepsPlace {P : Program} {env : XEnv} {R : State → XOutcome}
    (hR : ∀ s o, R s = o → ((∃ vals mem, o = .returned vals mem) ∨ ∃ e mem, o = .unwound e mem) →
      ∃ N, runLoopX env P N s.toX = o)
    (hP : ∀ g ∈ P.funcs, LinkFree g) (hS : ∀ g ∈ P.funcs, g.slots = [])
    (hk : XEnvKeepsPlace env) :
    XEnvKeepsPlace (linkEnvRX P env R) := by
  intro n gsem hg vals m
  cases hpf : P.func? n with
  | none => rw [linkEnvRX_none hpf] at hg; exact hk n gsem hg vals m
  | some g =>
    rw [linkEnvRX_some hpf] at hg
    cases hg
    cases hi : initState P n vals m with
    | ok s =>
      have hI := initState_xinv hi
      have key : ∀ o, R s = o → ((∃ vals mem, o = .returned vals mem) ∨
          ∃ e mem, o = .unwound e mem) →
          (∀ vals mem, o = .returned vals mem → mem.place = m.place) ∧
          (∀ e mem, o = .unwound e mem → mem.place = m.place) := by
        intro o ho hc
        obtain ⟨N, hN⟩ := hR s o ho hc
        cases hmp : m.place with
        | none =>
          have := runLoopX_placeNone hP hk N s.toX hI (initState_placeNone hi hmp)
          exact ⟨fun v mem h => this.1 v mem (h ▸ hN), fun e mem h => this.2 e mem (h ▸ hN)⟩
        | some pl =>
          have := runLoopX_placeI hP hS hk N s.toX hI (initState_placeI hS hi hmp)
          exact ⟨fun v mem h => this.1 v mem (h ▸ hN), fun e mem h => this.2 e mem (h ▸ hN)⟩
      refine ⟨fun rvals m' h => ?_, fun e m' h => ?_⟩
      · simp only [hi] at h
        exact (key _ h (.inl ⟨_, _, rfl⟩)).1 _ _ rfl
      · simp only [hi] at h
        exact (key _ h (.inr ⟨_, _, rfl⟩)).2 _ _ rfl
    | trap c => exact ⟨fun _ _ h => by simp [hi] at h, fun _ _ h => by simp [hi] at h⟩
    | stuck msg => exact ⟨fun _ _ h => by simp [hi] at h, fun _ _ h => by simp [hi] at h⟩

/-! ## The allocations -/

/-- **An exception propagating out of frames frees their slots**: the allocations after it are
the extern's not among the slots of the frames left, and a slot of a remaining frame is one of
the state's. -/
theorem unwindFrom_allocs (e : Exn) :
    ∀ (f : Frame) (cs : List (Frame × List ValueId)) (ts : List (Option ExnTable)) (mem : Mem),
      (∀ xs', unwindFrom e f cs ts mem = .next xs' → ∀ x ∈ xs'.s.mem.allocs, x ∈ mem.allocs ∧
        (x.base ∈ (f :: cs.map (·.1)).flatMap (fun fr => fr.slots.map (·.2)) →
          x.base ∈ slotBases xs'.s)) ∧
      (∀ e' m', unwindFrom e f cs ts mem = .unwound e' m' → ∀ x ∈ m'.allocs, x ∈ mem.allocs ∧
        x.base ∉ (f :: cs.map (·.1)).flatMap (fun fr => fr.slots.map (·.2)))
  | f, [], _, mem => by
    refine ⟨fun xs' h => by simp [unwindFrom] at h, fun e' m' h => ?_⟩
    simp only [unwindFrom, XStepResult.unwound.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro x hx
    rw [Mem.leave_allocs] at hx
    simp only [Mem.free, List.mem_filter, Bool.not_eq_true'] at hx
    obtain ⟨hx, hnb⟩ := hx
    refine ⟨hx, ?_⟩
    simpa using hnb
  | f, (c, rs) :: cs, t :: ts, mem => by
    have hf1 : ∀ x ∈ ((mem.free (f.slots.map (·.2))).leave).allocs, x ∈ mem.allocs ∧
        x.base ∉ f.slots.map (·.2) := by
      intro x hx
      rw [Mem.leave_allocs] at hx
      simp only [Mem.free, List.mem_filter, Bool.not_eq_true'] at hx
      exact ⟨hx.1, by simpa using hx.2⟩
    have ih := unwindFrom_allocs e c cs ts ((mem.free (f.slots.map (·.2))).leave)
    simp only [unwindFrom]
    split
    · rename_i r hr
      cases r with
      | ok fr' =>
        refine ⟨fun xs' h => ?_, fun e' m' h => by simp [XStepResult.ofRes] at h⟩
        simp only [XStepResult.ofRes, XStepResult.next.injEq] at h
        subst h
        obtain ⟨et, -, het⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨regs, bc, rfl⟩ := catchIn_ok het
        intro x hx
        obtain ⟨h1, h2⟩ := hf1 x hx
        refine ⟨h1, fun hb => ?_⟩
        simp only [List.map_cons, List.flatMap_cons, List.mem_append] at hb
        rcases hb with hb | hb
        · exact absurd hb h2
        · simpa [slotBases] using hb
      | trap c => exact ⟨fun _ h => by simp [XStepResult.ofRes] at h,
          fun _ _ h => by simp [XStepResult.ofRes] at h⟩
      | stuck m => exact ⟨fun _ h => by simp [XStepResult.ofRes] at h,
          fun _ _ h => by simp [XStepResult.ofRes] at h⟩
    · refine ⟨fun xs' h x hx => ?_, fun e' m' h x hx => ?_⟩
      · obtain ⟨h1, h2⟩ := ih.1 xs' h x hx
        obtain ⟨h3, h4⟩ := hf1 x h1
        refine ⟨h3, fun hb => h2 ?_⟩
        simp only [List.map_cons, List.flatMap_cons, List.mem_append] at hb ⊢
        rcases hb with hb | hb
        · exact absurd hb h4
        · exact hb
      · obtain ⟨h1, h2⟩ := ih.2 e' m' h x hx
        obtain ⟨h3, h4⟩ := hf1 x h1
        refine ⟨h3, fun hb => ?_⟩
        simp only [List.map_cons, List.flatMap_cons, List.mem_append] at hb h2
        rcases hb with hb | hb
        · exact h4 hb
        · exact h2 hb
  | f, _ :: _, [], mem => by
    exact ⟨fun _ h => by simp [unwindFrom] at h, fun _ _ h => by simp [unwindFrom] at h⟩

/-- **A whole-program step with unwinding keeps `AllocInv`** (when the externs create no
allocation). -/
theorem allocInvX_step {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : XEnvKeepsAllocs env) {cm : Mem} {xs : XState} (hI : XInv P xs)
    (hp : AllocInv cm xs.s) :
    (∀ xs', stepX env P xs = .next xs' → AllocInv cm xs'.s) ∧
    (∀ v m, stepX env P xs = .done v m → ∀ a k, m.valid a k = true → cm.valid a k = true) ∧
    (∀ e m, stepX env P xs = .unwound e m → ∀ a k, m.valid a k = true →
      cm.valid a k = true) := by
  unfold stepX
  split
  · rename_i e mem hr
    obtain ⟨n, g, vals, hg, hu⟩ := raiseAt_extern hr
    have hm : ∀ x ∈ mem.allocs, x ∈ xs.s.mem.allocs := (hk n g hg vals _).2 e mem hu
    have hU := unwindFrom_allocs e xs.s.frame xs.s.callers xs.tries mem
    refine ⟨fun xs' h => ?_, fun v m h => absurd h raiseIn_ne_done, fun e' m' h a k hv => ?_⟩
    · rcases raiseIn_cases h with ⟨fr', rfl, hsl⟩ | h
      · intro x hx
        rcases hp x (hm x hx) with h1 | h1
        · exact .inl h1
        · exact .inr (by simpa [slotBases, hsl] using h1)
      · intro x hx
        obtain ⟨h1, h2⟩ := hU.1 xs' h x hx
        rcases hp x (hm x h1) with h3 | h3
        · exact .inl h3
        · exact .inr (h2 (by simpa [slotBases] using h3))
    · simp only [Mem.valid, List.any_eq_true] at hv
      obtain ⟨x, hx, hc⟩ := hv
      obtain ⟨h1, h2⟩ := hU.2 e' m' (raiseIn_unwound h) x hx
      rcases hp x (hm x h1) with h3 | h3
      · exact h3 a k hc
      · exact absurd (by simpa [slotBases] using h3) h2
  · have hs := allocInv_step hP hk.toEnv hI.1 hp
    refine ⟨fun xs' h => ?_, fun v m h => ?_, fun e m h => ?_⟩
    · cases hst : step env.toEnv P xs.s with
      | next s1 =>
        rw [hst] at h
        simp only [liftStep, XStepResult.next.injEq] at h
        subst h
        exact hs.1 s1 hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s with
      | done v' m' =>
        rw [hst] at h
        simp only [liftStep, XStepResult.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hs.2 _ _ hst
      | _ => rw [hst] at h; simp [liftStep] at h
    · cases hst : step env.toEnv P xs.s <;> rw [hst] at h <;> simp [liftStep] at h

/-- **A returning or unwinding whole-program run with unwinding creates no allocation**: from a
state whose allocations are within `cm`'s valid bytes or slots of its frames, its memory is
valid only where `cm` is (when the externs create no allocation). -/
theorem runLoopX_allocs {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : XEnv}
    (hk : XEnvKeepsAllocs env) {cm : Mem} :
    ∀ (N : Nat) (xs : XState), XInv P xs → AllocInv cm xs.s →
      (∀ vals mem, runLoopX env P N xs = .returned vals mem →
        ∀ a k, mem.valid a k = true → cm.valid a k = true) ∧
      (∀ e mem, runLoopX env P N xs = .unwound e mem →
        ∀ a k, mem.valid a k = true → cm.valid a k = true)
  | 0, _, _, _ => ⟨fun _ _ h => by simp [runLoopX] at h, fun _ _ h => by simp [runLoopX] at h⟩
  | N + 1, xs, hI, hp => by
    have hs := allocInvX_step hP hk hI hp
    rw [runLoopX_succ']
    cases hst : stepX env P xs with
    | next xs' =>
      exact runLoopX_allocs hP hk N xs' (stepX_next_xinv hP hI hst) (hs.1 xs' hst)
    | done v m =>
      refine ⟨fun vals mem h => ?_, fun e mem h => by simp [afterStepX] at h⟩
      simp only [afterStepX, XOutcome.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.1 _ _ hst
    | unwound e m =>
      refine ⟨fun vals mem h => by simp [afterStepX] at h, fun e' mem h => ?_⟩
      simp only [afterStepX, XOutcome.unwound.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs.2.2 _ _ hst
    | trapped c => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩
    | stuck m => exact ⟨fun _ _ h => by simp [afterStepX] at h,
        fun _ _ h => by simp [afterStepX] at h⟩

/-! ## The run premises of a returning or unwinding run -/

/-- A run with unwinding that returns or unwinds never reaches a trapping step. -/
theorem reachX_not_trapped {env : XEnv} {p : Program} :
    ∀ {fuel : Nat} {xs0 : XState},
      ((∃ vals cm, runLoopX env p fuel xs0 = .returned vals cm) ∨
        ∃ e cm, runLoopX env p fuel xs0 = .unwound e cm) →
      ∀ {xs : XState}, ReachX env p xs0 xs → ∀ c, step env.toEnv p xs.s ≠ .trapped c := by
  intro fuel xs0 hrun xs hr
  induction hr generalizing fuel with
  | refl xs =>
    intro c hc
    have hx : stepX env p xs = .trapped c := by
      rw [stepX_of_not_stuck (fun msg e => by rw [hc] at e; cases e), hc]; rfl
    cases fuel with
    | zero => rcases hrun with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp [runLoopX] at h
    | succ n =>
      rcases hrun with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [runLoopX_succ', hx] at h <;>
        simp [afterStepX] at h
  | step hs _ ih =>
    cases fuel with
    | zero => rcases hrun with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp [runLoopX] at h
    | succ n =>
      rw [runLoopX_succ', hs] at hrun
      exact ih hrun

/-- **A returning or unwinding run with unwinding of the program without functions satisfies
the run premises** (`TrapsExplicitX`: it reaches no trapping step; its indirect calls enter no
function). -/
theorem trapsExplicitX_of_ended {env : XEnv} {P : Program} {cs : State} {fuel : Nat}
    (hrun : (∃ vals cm, runLoopX env P.bare fuel cs.toX = .returned vals cm) ∨
      ∃ e cm, runLoopX env P.bare fuel cs.toX = .unwound e cm) :
    TrapsExplicitX env P.bare cs where
  stmt := fun _ c _ _ hr hs _ => absurd hs (reachX_not_trapped hrun hr c)
  tryCall := fun _ c _ _ _ hr hs _ _ => absurd hs (reachX_not_trapped hrun hr c)
  tryCallInd := fun _ c _ _ _ hr hs _ _ => absurd hs (reachX_not_trapped hrun hr c)
  indirect := fun _ _ _ _ _ _ _ _ _ _ _ _ g hg => by simp at hg
  tryIndirect := fun _ _ _ _ _ _ _ _ _ _ g hg => by simp at hg

end Clif
