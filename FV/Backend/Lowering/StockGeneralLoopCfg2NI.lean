import FV.Backend.Lowering.StockParameterArgsCfgNI
import FV.Backend.Lowering.StockGeneralLoopCfg2
import FV.Backend.ABIReadCfg

namespace Backend.Stock.GeneralLoopCfg2.NI
set_option autoImplicit false

/-- Publish the proved general loop CFG class (all condition forms) as its actual unsplit Stock code; every
rejection uses the complete previous provider on the original function. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !sourceLeafEligible f then ParameterArgsCfg.NI.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock general loop CFG failed source and paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => ParameterArgsCfg.NI.lowerValidated f

/-- Retain all published routes and append the checked general loop provider as route 23. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  ParameterArgsCfg.NI.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.GeneralLoopCfg2.NI
