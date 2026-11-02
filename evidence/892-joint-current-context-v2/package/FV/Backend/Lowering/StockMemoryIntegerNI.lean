import FV.Backend.Lowering.StockMemoryCfgNI
import FV.Backend.StockMemoryIntegerCheck

namespace Backend.Stock.MemoryUnsigned
set_option autoImplicit false

/-- Add the proved unsigned widths with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryCfg.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock unsigned memory candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryCfg.lowerValidated f

/-- Keep published routes0–13 and append the unsigned memory provider as14. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryCfg.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemoryUnsigned
