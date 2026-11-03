import FV.E2E.UnwindMemoryFaultSource

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- The old explicit-only admission excludes memory fault events on every unwind path. -/
theorem TrapsExplicitX.no_memory_event {env : Clif.XEnv} {program : Clif.Program}
    {initial : Clif.State} (admitted : TrapsExplicitX env program initial)
    {xs : Clif.XState} {code : Clif.TrapCode} {address size : Nat}
    (reached : ReachX env program initial.toX xs) :
    ¬ Clif.MemTrapAt env.toEnv program xs.s code address size := by
  rintro ⟨trapped,invalid,statement,rest,body,access⟩
  have explicit := admitted.stmt xs code statement rest reached trapped body
  cases statement with
  | mk results inst => cases access <;> cases explicit

/-- The old branch derives its internal mapping instance without another caller premise. -/
theorem TrapsExplicitX.mapFaultsX {env : Clif.XEnv} {program : Clif.Program}
    {initial : Clif.State} (admitted : TrapsExplicitX env program initial)
    (mp : ArmFault.MemMap) : MapFaultsX mp env program initial := by
  intro xs code address size reached fault
  exact False.elim (admitted.no_memory_event reached fault)

/-- Existing unwind callers supply the complete new source interface internally. -/
theorem TrapsExplicitX.memory_interface {env : Clif.XEnv} {program : Clif.Program}
    {initial : Clif.State} (admitted : TrapsExplicitX env program initial)
    (mp : ArmFault.MemMap) :
    TrapsExplicitMX env program initial ∧ MapFaultsX mp env program initial :=
  ⟨admitted.toMX,admitted.mapFaultsX mp⟩

end E2E
