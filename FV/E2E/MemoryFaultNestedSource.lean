import FV.E2E.LinkMemoryFaultSource

namespace E2E.MemoryFaultSource
set_option autoImplicit false
set_option Elab.async false

/-- Every reached activation inherits mapping at its actual entry memory.
The original callers can contain any number of nested call frames. -/
theorem mapFaults_at_reached_activation {mp : ArmFault.MemMap}
    {env : Clif.Env} {program : Clif.Program} {initial reached : Clif.State}
    (mapped : MapFaults mp env program initial)
    (path : Clif.Reaches env program initial reached) :
    MapFaults mp env program ⟨reached.frame,[],reached.mem⟩ := by
  apply mapFaults_at_callee (callers := reached.callers) mapped
  exact reach_of_reaches path

/-- An actual source step supplies the next activation without an entry certificate.
This includes direct, indirect, try-call, and nested call entry steps. -/
theorem mapFaults_after_source_step {mp : ArmFault.MemMap}
    {env : Clif.Env} {program : Clif.Program} {initial before next : Clif.State}
    (mapped : MapFaults mp env program initial)
    (path : Clif.Reaches env program initial before)
    (stepped : Clif.step env program before = .next next) :
    MapFaults mp env program ⟨next.frame,[],next.mem⟩ :=
  mapFaults_at_reached_activation mapped (path.snoc stepped)

/-- The linked prefix constructs the full-source reachability used for the next activation. -/
theorem mapFaults_after_linked_source_step {mp : ArmFault.MemMap}
    {env linked : Clif.Env} {program : Clif.Program} {initial entry before next : Clif.State}
    (mapped : MapFaults mp env program initial)
    (lifted : ∀ target, Clif.Reaches linked program.bare entry target →
      Clif.Reaches env program initial target)
    (path : Clif.Reaches linked program.bare entry before)
    (stepped : Clif.step env program before = .next next) :
    MapFaults mp env program ⟨next.frame,[],next.mem⟩ :=
  mapFaults_after_source_step mapped (lifted before path) stepped

end E2E.MemoryFaultSource
