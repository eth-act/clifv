import FV.Backend.ReturnPinCheck
import FV.E2E.LinkReturnPins

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The executable check uses the exact return selection of the program model. -/
theorem returnPinCheck_pins (f : Clif.Function) (vc : VCode) :
    ReturnPinCheck.pins f vc = (ReturnPinMode.checked f vc).pins f (sigRets f.sig).length := by
  unfold ReturnPinCheck.pins ReturnPinMode.checked
  split
  · rfl
  · simp only [ReturnPinMode.pins,returnPins]
    split <;> rfl

/-- Actual call metadata derives the physical result relation internally. -/
theorem returnPinCheck_sound {definitions : List (Reg × Nat)} {f : Clif.Function} {vc : VCode}
    (checked : ReturnPinCheck.check (callDefs definitions) f vc = true) :
    CallReturnPins definitions (ReturnPinCheck.pins f vc) := by
  simpa only [ReturnPinCheck.check,decide_eq_true_eq,callDefs,List.map_map,
    Function.comp_def,List.length_map,CallReturnPins] using checked

/-- Every ordinary checker branch retains the exact old call-register verdict. -/
theorem returnPinCheck_previous {definitions : List (Reg × Nat)} {f : Clif.Function} {vc : VCode}
    (old : SemanticNI.check f vc = true) :
    ReturnPinCheck.check (callDefs definitions) f vc =
      decide ((definitions.map (·.1)).take (sigRets f.sig).length =
        (List.range (min (sigRets f.sig).length definitions.length)).map Reg.x) := by
  simp only [ReturnPinCheck.check,ReturnPinCheck.pins,old,↓reduceIte,callDefs,
    List.map_map,Function.comp_def,List.length_map,List.length_range,← List.map_take,
    List.take_range,Nat.min_comm]

/-- Stock calls that ignore implicit sret results need no surplus physical definition. -/
theorem returnPinCheck_ignored (f : Clif.Function) (vc : VCode) :
    ReturnPinCheck.check [] f vc = true := by
  simp only [ReturnPinCheck.check,List.map_nil,List.take_nil,List.length_nil,List.take_zero,
    decide_true]

end E2E
