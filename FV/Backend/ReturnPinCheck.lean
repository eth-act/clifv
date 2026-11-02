import FV.Backend.SemanticNICheck

namespace Backend.ReturnPinCheck
set_option autoImplicit false

/-- Select return registers from the actual checker branch and original signature. -/
def pins (f : Clif.Function) (vc : VCode) : List Reg :=
  let count := (sigRets f.sig).length
  if SemanticNI.check f vc then (List.range count).map Reg.x
  else if (sigRets f.sig).any (·.purpose == .sret) then [.x 8]
  else (retRegs count).getD []

/-- Check the common prefix of actual call definitions and callee return registers. -/
def check (definitions : List (Reg × Reg)) (f : Clif.Function) (vc : VCode) : Bool :=
  let selected := pins f vc
  decide ((definitions.map (·.1)).take selected.length = selected.take definitions.length)

end Backend.ReturnPinCheck
