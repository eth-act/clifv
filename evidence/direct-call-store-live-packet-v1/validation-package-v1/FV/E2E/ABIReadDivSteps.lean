import FV.Backend.ABIReadDiv
import FV.E2E.ABIReadFlagsSteps
namespace E2E.DivRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

theorem no_mem {i : MInst} (checked : Backend.ABIReadDiv.additional i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadDiv.additional i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked

/-- Trapping guards retain all original physical ABI reads. A true guard
terminates; a false guard and a quotient continue normally; `udf` terminates. -/
theorem step_frame {i : MInst} (checked : Backend.ABIReadDiv.additional i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) :
    FlagFrame w t ∧ (ctl = .next ∨ ctl = .ret ∨ ctl = .halt) := by
  rw [spec_eq checked] at run
  cases i with
  | aluRRR op sz rd rn rm =>
    cases op <;> try cases checked
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
            exact ⟨FlagFrame.refl _,Or.inl rfl⟩
  | aluRRImm12 op sz rd rn imm =>
    cases op <;> try cases checked
    all_goals cases rd <;> try cases checked
    all_goals cases rn <;> try cases checked
    all_goals
      cases us with
      | nil => cases run
      | cons a rest =>
        cases rest with
        | cons => cases run
        | nil =>
          simp only [ispec] at run
          split at run
          · simp only [Option.some.injEq,Prod.mk.injEq] at run
            obtain ⟨rfl,rfl,rfl⟩ := run
            exact ⟨FlagFrame.write_pstate _ _,Or.inl rfl⟩
          · cases run
  | ccmpImm sz rn imm nzcv c =>
    cases rn <;> try cases checked
    all_goals
      cases us with
      | nil => cases run
      | cons a rest =>
        cases rest with
        | cons => cases run
        | nil =>
          simp only [ispec] at run
          split at run
          · simp only [Option.some.injEq,Prod.mk.injEq] at run
            obtain ⟨rfl,rfl,rfl⟩ := run
            exact ⟨FlagFrame.write_pstate _ _,Or.inl rfl⟩
          · cases run
  | trapIf kind code =>
    simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    refine ⟨FlagFrame.refl _,?_⟩
    split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
  | udf code =>
    cases us with
    | cons => cases run
    | nil =>
      simp only [ispec,Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      exact ⟨FlagFrame.refl _,Or.inr (Or.inr rfl)⟩
  | _ => cases checked
end E2E.DivRead
