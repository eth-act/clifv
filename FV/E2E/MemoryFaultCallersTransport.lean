import FV.E2E.MemoryFaultSourceTransport
import FV.E2E.LinkClifN

namespace E2E.MemoryFaultSource
open Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The source interpreter and the driver use the same continuing-step paths. -/
theorem reaches_of_reach {env : Clif.Env} {p : Clif.Program} {s t : Clif.State}
    (path : Reach env p s t) : Clif.Reaches env p s t := by
  induction path with
  | refl => exact .refl _
  | step stepped rest ih => exact .next stepped ih

theorem reach_of_reaches {env : Clif.Env} {p : Clif.Program} {s t : Clif.State}
    (path : Clif.Reaches env p s t) : Reach env p s t := by
  induction path with
  | refl => exact .refl _
  | next stepped rest ih => exact .step stepped ih

/-- Existing interpreter stack transport preserves every continuing source step. -/
theorem reach_under_callers {env : Clif.Env} {p : Clif.Program} {s t : Clif.State}
    (callers : List (Clif.Frame × List Clif.ValueId)) (path : Reach env p s t) :
    Reach env p (s.below callers) (t.below callers) :=
  reach_of_reaches ((reaches_of_reach path).under callers)

/-- The original mapping fact covers the callee before it returns to its extra callers. -/
theorem mapFaults_without_callers {mp : ArmFault.MemMap} {env : Clif.Env} {p : Clif.Program}
    {entry : Clif.State} {callers : List (Clif.Frame × List Clif.ValueId)}
    (mapped : MapFaults mp env p (entry.below callers)) : MapFaults mp env p entry := by
  apply mapFaults_of_reach_simulation mapped
  intro state path
  exact ⟨state.below callers,reach_under_callers callers path,rfl,rfl⟩

/-- A reached callee inherits the full-program mapping fact with its original memory. -/
theorem mapFaults_at_callee {mp : ArmFault.MemMap} {env : Clif.Env} {p : Clif.Program}
    {initial callee : Clif.State} {callers : List (Clif.Frame × List Clif.ValueId)}
    (mapped : MapFaults mp env p initial)
    (entered : Reach env p initial (callee.below callers)) : MapFaults mp env p callee :=
  mapFaults_without_callers (mapFaults_of_reach mapped entered)

end E2E.MemoryFaultSource
