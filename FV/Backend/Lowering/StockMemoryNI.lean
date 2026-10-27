import FV.Backend.Lowering.StockParameterCfgNI
import FV.Backend.StockMemoryCheck

namespace Backend.Stock.Memory
set_option autoImplicit false

/-- Attempt the first proved memory class, then preserve the complete previous
provider on the original source when selection or validation fails. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then ParameterCfg.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock memory candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => ParameterCfg.lowerValidated f

/-- Retain published routes0–11; memory delivery appends route12. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  ParameterCfg.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.Memory
