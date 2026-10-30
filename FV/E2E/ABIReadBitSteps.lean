import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps



namespace E2E.BitRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

private theorem same_frame {outs' outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : some (outs',w,Ctl.next) = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  simp only [Option.some.injEq,Prod.mk.injEq] at run
  obtain ⟨rfl,rfl,rfl⟩ := run
  exact ⟨FlagFrame.refl _,rfl⟩

theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.bitProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  cases i with
  | bitRR op sz rd rn =>
    cases op <;> cases sz
    all_goals
      cases us with
      | nil => simp [mspec,ispec] at run
      | cons a rest =>
        cases rest with
        | nil => first | exact same_frame run | simp [mspec,ispec] at run
        | cons b tail => simp [mspec,ispec] at run
  | aluRRR op sz rd rn rm =>
    cases op <;> try cases checked
    all_goals cases sz
    all_goals
      cases us with
      | nil => simp [mspec,ispec] at run
      | cons a rest =>
        cases rest with
        | nil =>
          cases rn <;> cases rm <;> simp only [mspec,ispec,rrrVal,Option.map_some] at run
          all_goals first | exact same_frame run | cases run
        | cons b tail =>
          cases tail with
          | cons c rest => simp [mspec,ispec] at run
          | nil =>
            simp only [mspec,ispec,rrrVal,shiftVal,Option.map_some] at run
            all_goals exact same_frame run
  | aluRRImmShift op sz rd rn imm =>
    cases op <;> try cases checked
    all_goals
      cases us with
      | nil => simp [mspec,ispec] at run
      | cons a rest =>
        cases rest with
        | cons b tail => simp [mspec,ispec] at run
        | nil =>
          simp only [mspec,ispec] at run
          split at run
          · simp only [shiftVal,Option.map_some] at run
            exact same_frame run
          · simp [mspec,ispec] at run
  | aluRRRShift op sz rd rn rm sh =>
    cases op <;> try cases checked
    cases us with
    | nil => simp [mspec,ispec] at run
    | cons a rest =>
      cases rest with
      | nil => cases rn <;> simp [mspec,ispec,aluShiftable] at run
      | cons b tail =>
        cases tail with
        | cons c rest => simp [mspec,ispec] at run
        | nil =>
          simp only [mspec,ispec] at run
          split at run
          · exact same_frame run
          · cases run
  | _ => cases checked

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.bitProducer i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.bitProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked
end E2E.BitRead
