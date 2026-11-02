import FV.E2E.CallReturnPins

namespace E2E.CallReturnPinsWitness
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private def state : Arm.ArmState := Arm.write_base_gpr 8#5 37 Arm.ArmState.default
private def other : Arm.ArmState := Arm.write_base_gpr 10#5 99 state
private def uses : List (Reg × Reg) := [(.vreg 9 .int,.x 8)]
private def definitions : List (Reg × Nat) := [(.x 8,12)]
private def operands : Array Operand := (callDefOps definitions).toArray
private def registers : Array Reg := #[.x 8]

private theorem returned {s : Arm.ArmState} (pc : Arm.r .PC s = 0)
    (error : Arm.r .ERR s = .None) (value : regVal s (.x 8) = 37) :
    ActRet 0 (fun _ => False) (fun _ => False) uses [37] s s s := by
  refine ⟨⟨pc,error,rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩,?_,fun _ _ => rfl,
    fun _ _ _ _ => rfl,fun _ _ => rfl,rfl⟩
  intro j v pin x found output
  cases j with
  | zero =>
    simp only [uses,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl⟩ := found
    simp only [List.getElem?_cons_zero,Option.some.injEq] at output
    rw [← output]
    exact value
  | succ j => simp [uses] at found

/-- A nonzero x8 return and distinct worlds inhabit the generic call-result proof.
An x0 caller definition is rejected for the same return pin. -/
theorem x8_call_result_witness :
    Arm.r (.GPR 10#5) state ≠ Arm.r (.GPR 10#5) other ∧
      CallReturnPins definitions [.x 8] ∧ ¬ CallReturnPins [(.x 0,12)] [.x 8] ∧
      (∀ pair ∈ defRegs operands registers ([.x 8].map (regVal other)),
        regVal state pair.1.2 = pair.2) := by
  have first := returned (s := state) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have second := returned (s := other) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have same : ∀ pin ∈ [.x 8],regVal state pin = regVal other pin :=
    first.pins_agree second rfl
  have matched : CallReturnPins definitions [.x 8] := by unfold CallReturnPins; decide +kernel
  have allocated : ((operands.zip registers).toList.filter (·.1.isDef)) =
      (callDefOps definitions).zip (definitions.map (·.1)) := by decide +kernel
  exact ⟨by decide +kernel,matched,by unfold CallReturnPins; decide +kernel,matched.defRegs allocated same⟩

end E2E.CallReturnPinsWitness
