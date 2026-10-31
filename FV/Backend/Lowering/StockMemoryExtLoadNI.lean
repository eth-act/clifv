import FV.Backend.Lowering.StockMemoryIntegerNI
import FV.Backend.StockMemoryExtLoadCheck

namespace Backend.Stock.MemoryExtending
set_option autoImplicit false

/-- Add the proved extending forms with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryUnsigned.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock extending memory candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryUnsigned.lowerValidated f

/-- Keep published routes0–14 and append the extending memory provider as15. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryUnsigned.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemoryExtending
