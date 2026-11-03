import FV.E2E.UnwindMemoryFaultExplicit

namespace E2E
set_option autoImplicit false

/-- A source observation retains the actual handler context and its memory event. -/
def UnwindMemoryFaultEvent (env : Clif.XEnv) (program : Clif.Program)
    (initial : Clif.State) (code : Clif.TrapCode) : Prop :=
  ∃ xs address size, ReachX env program initial.toX xs ∧
    Clif.MemTrapAt env.toEnv program xs.s code address size

/-- A memory event takes the ordinary trap branch of the actual unwind step. -/
theorem memory_event_stepX {env : Clif.XEnv} {program : Clif.Program}
    {xs : Clif.XState} {code : Clif.TrapCode} {address size : Nat}
    (event : Clif.MemTrapAt env.toEnv program xs.s code address size) :
    Clif.stepX env program xs = .trapped code := by
  obtain ⟨trapped,invalid,statement,rest,body,access⟩ := event
  have noRaise : Clif.raiseAt? env program xs.s = none := by
    unfold Clif.raiseAt?
    rw [body]
    cases statement with
    | mk results inst => cases access <;> rfl
  simp only [Clif.stepX,noRaise,trapped,Clif.liftStep]

/-- Continuing unwind steps preserve the exact later source trap. -/
theorem ReachX.trapped_run {env : Clif.XEnv} {program : Clif.Program}
    {initial last : Clif.XState} {code : Clif.TrapCode}
    (reached : ReachX env program initial last)
    (trapped : Clif.stepX env program last = .trapped code) :
    ∃ fuel, Clif.runLoopX env program fuel initial = .trapped code := by
  induction reached with
  | refl => exact ⟨1,by simp only [Clif.runLoopX,trapped]⟩
  | step next _ ih =>
    obtain ⟨fuel,run⟩ := ih trapped
    exact ⟨fuel+1,by simpa only [Clif.runLoopX,next] using run⟩

/-- This is a source-run observation. It does not assert a hardware memory fault. -/
theorem UnwindMemoryFaultEvent.source_trapped {env : Clif.XEnv} {program : Clif.Program}
    {initial : Clif.State} {code : Clif.TrapCode}
    (event : UnwindMemoryFaultEvent env program initial code) :
    ∃ fuel, Clif.runLoopX env program fuel initial.toX = .trapped code := by
  obtain ⟨xs,address,size,reached,memory⟩ := event
  exact reached.trapped_run (memory_event_stepX memory)

/-- The old explicit-only input excludes this separate memory observation. -/
theorem UnwindMemoryFaultEvent.excluded_by_original {env : Clif.XEnv}
    {program : Clif.Program} {initial : Clif.State} {code : Clif.TrapCode}
    (admitted : TrapsExplicitX env program initial) :
    ¬ UnwindMemoryFaultEvent env program initial code := by
  rintro ⟨xs,address,size,reached,event⟩
  exact admitted.no_memory_event reached event

end E2E
