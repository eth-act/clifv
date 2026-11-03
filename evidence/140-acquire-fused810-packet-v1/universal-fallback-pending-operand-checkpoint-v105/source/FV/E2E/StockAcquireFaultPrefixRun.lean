import FV.E2E.StockAcquireModelStepF

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual local step transfers compose through precisely the finite prefix before the fault. -/
theorem runF_eq_model_prefix {mp : ArmFault.MemMap} {model : Arm.ArmState → Arm.ArmState}
    {n : Nat} {initial : Arm.ArmState}
    (localStep : ∀ j < n,ArmFault.stepF mp (runX model j initial) = model (runX model j initial)) :
    ArmFault.runF mp n initial = runX model n initial := by
  revert localStep
  induction n with
  | zero => intro localStep;rfl
  | succ n ih =>
    intro localStep
    rw [ArmFault.runF_succ',ih (fun j inside => localStep j (by omega)),runX_add]
    exact localStep n (Nat.lt_succ_self n)

/-- The final source-mapped fault stays fixed after every earlier fault-aware model step succeeds. -/
theorem runF_first_model_fault {mp : ArmFault.MemMap} {model : Arm.ArmState → Arm.ArmState}
    {n : Nat} {initial : Arm.ArmState}
    (localStep : ∀ j < n,ArmFault.stepF mp (runX model j initial) = model (runX model j initial))
    (fault : ArmFault.Faults mp (runX model n initial)) :
    ArmFault.runF mp (n+1) initial = Arm.write_err ArmFault.memFault (runX model n initial) := by
  rw [ArmFault.runF_succ',runF_eq_model_prefix localStep]
  exact ArmFault.stepF_fault fault

end E2E.StockAcquirePending
