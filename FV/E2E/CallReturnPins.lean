import FV.E2E.LinkWorld

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Caller definitions and callee return pins agree on their common prefix. -/
def CallReturnPins (definitions : List (Reg × Nat)) (pins : List Reg) : Prop :=
  (definitions.map (·.1)).take pins.length = pins.take definitions.length

/-- The previous x0-order call condition retains its exact meaning. -/
theorem CallReturnPins.ordinary {definitions : List (Reg × Nat)} {count : Nat}
    (ordered : (definitions.map (·.1)).take count =
      (List.range (min count definitions.length)).map Reg.x) :
    CallReturnPins definitions ((List.range count).map Reg.x) := by
  simpa only [CallReturnPins,List.length_map,List.length_range,← List.map_take,List.take_range,Nat.min_comm]
    using ordered

/-- Equal return values agree in every actual return pin, including x8. -/
theorem ActRet.pins_agree {ra ra' : BitVec 64} {F G F' G' : BitVec 64 → Prop}
    {us : List (Reg × Reg)} {outs : List CV} {w s t w' s' t' : Arm.ArmState}
    (first : ActRet ra F G us outs w s t) (second : ActRet ra' F' G' us outs w' s' t')
    (arity : us.length = outs.length) :
    ∀ pin ∈ us.map (·.2),regVal t pin = regVal t' pin := by
  intro pin member
  obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp present
  have inside : j < outs.length := by rw [← arity]; exact lt_of_getElem? found
  have value : outs[j]? = some outs[j] := List.getElem?_eq_getElem inside
  rw [first.regs j pair.1 pair.2 _ found value,second.regs j pair.1 pair.2 _ found value]

/-- The actual return-pin relation supplies every declared physical call result. -/
theorem CallReturnPins.defRegs {definitions : List (Reg × Nat)} {pins : List Reg}
    (matched : CallReturnPins definitions pins) {ops : Array Operand} {regs : Array Reg}
    (allocated : ((ops.zip regs).toList.filter (·.1.isDef)) =
      (callDefOps definitions).zip (definitions.map (·.1)))
    {actual reference : Arm.ArmState}
    (same : ∀ pin ∈ pins,regVal actual pin = regVal reference pin) :
    ∀ pair ∈ defRegs ops regs (pins.map (regVal reference)),
      regVal actual pair.1.2 = pair.2 := by
  intro pair member
  obtain ⟨⟨op,pin⟩,value⟩ := pair
  rw [Backend.Proof.defRegs,allocated] at member
  obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
  simp only [List.getElem?_zip_eq_some] at found
  obtain ⟨⟨_,defined⟩,returned⟩ := found
  have pinBound : j < pins.length := by
    have bound := lt_of_getElem? returned
    simpa only [List.length_map] using bound
  have defBound : j < definitions.length := by
    have bound := lt_of_getElem? defined
    simpa only [List.length_map] using bound
  have selected : ((definitions.map (·.1)).take pins.length)[j]? =
      (definitions.map (·.1))[j]? := by
    rw [List.getElem?_take]
    simp only [pinBound,ite_true]
  have returnedPin : pins[j]? = some pin := by
    rw [← selected,matched] at defined
    simpa only [List.getElem?_take,defBound,ite_true] using defined
  have valueEq : regVal reference pin = value := by
    simpa only [List.getElem?_map,returnedPin,Option.map_some,Option.some.injEq] using returned
  rw [← valueEq]
  exact same pin (List.mem_of_getElem? returnedPin)

end E2E
