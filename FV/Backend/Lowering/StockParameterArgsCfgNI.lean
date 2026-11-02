import FV.Backend.Lowering.StockVoidCallNI
import FV.Backend.Lowering.StockParameterArgsCfg
import FV.Backend.ABIReadCfg

namespace Backend.Stock.ParameterArgsCfg.NI
set_option autoImplicit false

/-- Publish the proved argument-passing CFG class as its actual split code; every rejection uses
the complete previous provider on the original function. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !sourceLeafEligible f then VoidCall.NI.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      let split ← splitEdgesChecked result.code result.edgeArgs
      if check f split.code && ABIReadCfg.check f.sig split.code then pure split.code
      else throw "Stock argument-passing CFG failed source and paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => VoidCall.NI.lowerValidated f

/-- Retain all published routes and append the checked argument-passing provider as route 22. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  VoidCall.NI.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.ParameterArgsCfg.NI
