import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps
namespace E2E.BooleanRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.booleanProducer i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.booleanProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked

/-- CSET writes its virtual result while retaining all physical ABI reads,
memory and flags. -/
theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.booleanProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  rw [spec_eq checked] at run
  cases i with
  | cset rd c =>
    cases rd <;> try cases checked
    case vreg d cls =>
      cases cls <;> try cases checked
      cases us with
      | cons => cases run
      | nil =>
        simp only [ispec] at run
        split at run
        · cases run
        · simp only [Option.some.injEq,Prod.mk.injEq] at run
          obtain ⟨rfl,rfl,rfl⟩ := run
          exact ⟨FlagFrame.refl _,rfl⟩
  | _ => cases checked
end E2E.BooleanRead
