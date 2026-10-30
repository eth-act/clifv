import FV.Backend.ABIReadScalar
import FV.E2E.ABIReadFlagsSteps
namespace E2E.CastRead
open Backend Backend.Proof Backend.Proof.Driver E2E.MixedFlagBoundary
set_option autoImplicit false
set_option Elab.async false

private theorem extension_cases {i : MInst} (checked : Backend.ABIReadScalar.extension i = true) :
    ∃ rd rn sg fromB toB,i = .extend rd rn sg fromB toB ∧
      ((fromB=8 ∧ toB=16) ∨ (fromB=8 ∧ toB=32) ∨ (fromB=8 ∧ toB=64) ∨
       (fromB=16 ∧ toB=32) ∨ (fromB=16 ∧ toB=64) ∨ (fromB=32 ∧ toB=64)) := by
  cases i with
  | extend rd rn sg fromB toB =>
    have member : (fromB,toB) ∈ [(8,16),(8,32),(8,64),(16,32),(16,64),(32,64)] :=
      List.contains_iff_mem.mp checked
    refine ⟨rd,rn,sg,fromB,toB,rfl,?_⟩
    simpa only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] using member
  | _ => cases checked

private theorem same_frame {outs' outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : some (outs',w,Ctl.next) = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  simp only [Option.some.injEq,Prod.mk.injEq] at run
  obtain ⟨rfl,rfl,rfl⟩ := run
  exact ⟨FlagFrame.refl _,rfl⟩

/-- Both signedness choices and every supported extension width preserve ABI
reads, all world fields and ordinary control. -/
theorem step_frame {i : MInst} (checked : Backend.ABIReadScalar.extension i = true) {sb : Nat}
    {us outs : List CV} {w t : Arm.ArmState} {ctl : Ctl}
    (run : mspec sb i us w = some (outs,t,ctl)) : FlagFrame w t ∧ ctl = .next := by
  obtain ⟨rd,rn,sg,fromB,toB,rfl,widths⟩ := extension_cases checked
  rcases widths with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    cases us with
    | nil => cases run
    | cons a rest =>
      cases rest with
      | nil => exact same_frame run
      | cons b tail => cases run

theorem no_mem {i : MInst} (checked : Backend.ABIReadScalar.extension i = true) : i.isMemAcc = false := by
  cases i <;> first | rfl | cases checked

theorem spec_eq {i : MInst} (checked : Backend.ABIReadScalar.extension i = true) (sb : Nat)
    (us : List CV) (w : Arm.ArmState) : mspec sb i us w = ispec i us w := by
  cases i <;> first | rfl | cases checked
end E2E.CastRead
