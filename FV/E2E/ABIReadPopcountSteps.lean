import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps
namespace E2E.PopcountRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

private theorem same_frame {outs' outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : some (outs',w,Ctl.next) = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  simp only [Option.some.injEq,Prod.mk.injEq] at run
  obtain ⟨rfl,rfl,rfl⟩ := run
  exact ⟨FlagFrame.refl _,rfl⟩

theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.popcountProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  cases i with
  | movToFpu rd rn sz =>
    cases sz <;> try cases checked
    all_goals
      cases us with
      | nil => cases run
      | cons a rest =>
        cases rest with
        | nil => exact same_frame run
        | cons b tail => cases run
  | movFromVec rd rn idx sz =>
    cases idx <;> try cases checked
    cases sz <;> try cases checked
    cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => exact same_frame run
      | cons b tail => cases run
  | vecMisc op rd rn sz =>
    cases op <;> cases sz <;> try cases checked
    cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => exact same_frame run
      | cons b tail => cases run
  | vecLanes op rd rn sz =>
    cases op <;> cases sz <;> try cases checked
    cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => exact same_frame run
      | cons b tail => cases run
  | vecRRR op rd rn rm sz =>
    cases op <;> cases sz <;> try cases checked
    cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => cases run
      | cons b tail =>
        cases tail with
        | nil => exact same_frame run
        | cons c tail => cases run
  | _ => cases checked

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.popcountProducer i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.popcountProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked
end E2E.PopcountRead
