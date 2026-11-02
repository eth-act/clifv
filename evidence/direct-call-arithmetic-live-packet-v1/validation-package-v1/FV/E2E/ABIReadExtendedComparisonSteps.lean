import FV.E2E.ABIReadFlagsSteps
import FV.Backend.ABIReadScalar

namespace E2E.ExtendedComparisonRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

theorem cases_of_check {i : MInst}
    (checked : Backend.ABIReadScalar.extendedComparisonProducer i = true) :
    (∃ sz n m e,i = .aluRRRExtend .subS sz .xzr (.vreg n .int) (.vreg m .int) e) ∨
    (∃ sz n imm,i = .aluRRImmLogic .andS sz .xzr (.vreg n .int) imm) := by
  cases i with
  | aluRRRExtend op sz rd rn rm e =>
    cases op <;> try cases checked
    cases rd <;> try cases checked
    cases rn <;> try cases checked
    case vreg n cls =>
      cases cls <;> try cases checked
      cases rm <;> try cases checked
      case vreg m cls =>
        cases cls <;> try cases checked
        exact Or.inl ⟨sz,n,m,e,rfl⟩
  | aluRRImmLogic op sz rd rn imm =>
    cases op <;> try cases checked
    cases rd <;> try cases checked
    cases rn <;> try cases checked
    case vreg n cls =>
      cases cls <;> try cases checked
      exact Or.inr ⟨sz,n,imm,rfl⟩
  | _ => cases checked

theorem no_mem {i : MInst}
    (checked : Backend.ABIReadScalar.extendedComparisonProducer i = true) :
    i.isMemAcc = false := by
  rcases cases_of_check checked with ⟨sz,n,m,e,rfl⟩ | ⟨sz,n,imm,rfl⟩ <;> rfl

theorem spec_eq {i : MInst}
    (checked : Backend.ABIReadScalar.extendedComparisonProducer i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  rcases cases_of_check checked with ⟨sz,n,m,e,rfl⟩ | ⟨sz,n,imm,rfl⟩ <;> rfl

/-- Only flags change: original physical ABI registers and memory are framed. -/
theorem step_frame {i : MInst}
    (checked : Backend.ABIReadScalar.extendedComparisonProducer i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  rw [spec_eq checked] at run
  rcases cases_of_check checked with ⟨sz,n,m,e,rfl⟩ | ⟨sz,n,imm,rfl⟩
  · cases us with
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
  · cases us with
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

end E2E.ExtendedComparisonRead
