import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps
namespace E2E.HighMulRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.highmulProducer i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.highmulProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked

/-- Exact scalar high products frame all original physical ABI reads and flags. -/
theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.highmulProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  rw [spec_eq checked] at run
  cases i with
  | aluRRR op sz rd rn rm =>
    cases op <;> try cases checked
    all_goals cases sz <;> try cases checked
    all_goals cases rd <;> try cases checked
    all_goals cases rn <;> try cases checked
    all_goals cases rm <;> try cases checked
    all_goals
      cases us with
      | nil => cases run
      | cons a rest =>
        cases rest with
        | nil => cases run
        | cons b tail =>
          cases tail with
          | cons => cases run
          | nil =>
            simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
            obtain ⟨rfl,rfl,rfl⟩ := run
            exact ⟨FlagFrame.refl _,rfl⟩
  | _ => cases checked
end E2E.HighMulRead
