import FV.E2E.ExtSemGuard

/-!
# Witnesses for `FV/E2E/ExtSemGuard.lean`

* `guard_keeps`: a call semantics whose result satisfies the guard keeps it; `guard_replaces`:
  one whose result does not is replaced by an accepted one;
* `guard_contracts`: `xCallsOk_guard`/`xCallsIndOk_guard` apply (no externs, no indirect call:
  every result is accepted).
-/

namespace E2E.ExtSemGuardWitness

open Backend Backend.Proof

/-- `Y` with calls that return no values and the world unchanged. -/
def X0 (Y : ExtSem) : ExtSem := { Y with call := fun _ _ w => some ([], w) }

theorem guard_keeps (Y : ExtSem) (w : Arm.ArmState) :
    ((X0 Y).guard fun _ _ w' r => r = ([], w')).call none [] w = some ([], w) :=
  ExtSem.guard_of rfl rfl

theorem guard_replaces (Y : ExtSem) (w : Arm.ArmState) :
    (X0 Y).call none [] w = some ([], w) ∧
      ∃ r, ((X0 Y).guard fun _ _ _ r => r.1 = [0]).call none [] w = some r ∧ r.1 = [0] :=
  ⟨rfl, ExtSem.guard_spec ⟨([0], w), rfl⟩⟩

theorem guard_contracts (Y : ExtSem) (env : Clif.Env) (MR : MemRelT) :
    XCallsOk env [] MR ((X0 Y).guard (CallPost env [] [] MR (X0 Y).sym)) ∧
      XCallsIndOk env [] MR ((X0 Y).guard (CallPost env [] [] MR (X0 Y).sym)) := by
  have hex : ∀ d uses w, ∃ r, CallPost env [] [] MR (X0 Y).sym d uses w r :=
    fun _ _ w => ⟨([], w), by simp [CallPost]⟩
  exact ⟨xCallsOk_guard (X0 Y) hex, xCallsIndOk_guard (X0 Y) hex⟩

end E2E.ExtSemGuardWitness
