import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps
namespace E2E.MaskRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.maskProducer i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.maskProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked

/-- CSETM writes its virtual result while retaining all physical ABI reads,
memory and flags. -/
theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.maskProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  rw [spec_eq checked] at run
  cases i with
  | csetm rd c =>
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
/-- A genuine virtual CSETM call inhabits all three ABI-frame contracts. -/
theorem step_frame_witness :
    ∃ outs,mspec 0 (.csetm (.vreg 0 .int) .ne) [] Arm.ArmState.default =
      some (outs,Arm.ArmState.default,.next) ∧ FlagFrame Arm.ArmState.default Arm.ArmState.default := by
  refine ⟨_,rfl,?_⟩
  exact (step_frame (show Backend.ABIReadScalar.maskProducer (.csetm (.vreg 0 .int) .ne) = true from rfl)
    (show mspec 0 (.csetm (.vreg 0 .int) .ne) [] Arm.ArmState.default = some (_,Arm.ArmState.default,.next) from rfl)).1
end E2E.MaskRead
