import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps
namespace E2E.ComparisonRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.comparisonProducer i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.comparisonProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked

/-- Actual comparison flags change while all original physical ABI reads are retained. -/
theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.comparisonProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  rw [spec_eq checked] at run
  cases i with
  | aluRRR op sz rd rn rm =>
    cases op <;> try cases checked
    cases rd <;> try cases checked
    cases rn <;> try cases checked
    case vreg n cls =>
      cases cls <;> try cases checked
      cases rm <;> try cases checked
      case vreg m cls =>
        cases cls <;> try cases checked
        cases us with
        | nil => cases run
        | cons a rest =>
          cases rest with
          | nil => cases run
          | cons b tail =>
            cases tail with
            | cons c rest => cases run
            | nil =>
              simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
              obtain ⟨rfl,rfl,rfl⟩ := run
              exact ⟨FlagFrame.write_pstate _ _,rfl⟩
  | aluRRImm12 op sz rd rn imm =>
    cases op <;> try cases checked
    all_goals cases rd <;> try cases checked
    all_goals cases rn <;> try cases checked
    all_goals rename_i n cls
    all_goals cases cls <;> try cases checked
    all_goals
      cases us with
      | nil => cases run
      | cons a rest =>
        cases rest with
        | cons b tail => cases run
        | nil =>
          simp only [ispec] at run
          split at run
          · simp only [Option.some.injEq,Prod.mk.injEq] at run
            obtain ⟨rfl,rfl,rfl⟩ := run
            exact ⟨FlagFrame.write_pstate _ _,rfl⟩
          · cases run
  | _ => cases checked
end E2E.ComparisonRead
