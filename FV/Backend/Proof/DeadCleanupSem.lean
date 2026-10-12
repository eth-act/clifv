import FV.Backend.Proof.DeadCleanupStructure
import FV.Backend.Proof.RegallocCSemWorld

namespace Backend.DeadCleanup
open Backend.Proof

set_option maxHeartbeats 4000000 in
/-- The value-level specification confirms that a whitelisted instruction
changes neither the world nor control. This alone is not a whole-pass theorem:
the concrete semantics also has canonical-register bookkeeping. -/
theorem mspec_pure {sb : Nat} {i : MInst} {us outs : List CV}
    {w w' : Arm.ArmState} {ctl : Ctl} (hp : pureForm i = true)
    (h : mspec sb i us w = some (outs, w', ctl)) : w' = w ∧ ctl = .next := by
  unfold mspec at h
  split at h <;> try { simp_all [pureForm, pureAlu] }
  unfold ispec at h
  split at h <;> simp_all [pureForm, pureAlu, Option.map_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq]
  all_goals grind only

example (w : Arm.ArmState) : ∃ outs,
    mspec 0 deadMvn [0#128] w = some (outs, w, .next) := by
  exact ⟨[ofX (~~~(0#64))], rfl⟩

end Backend.DeadCleanup
