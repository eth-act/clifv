import FV.Backend.Lowering.StockMemoryCapturedCopyNI
import FV.Backend.StockMemorySretCopyCheck

namespace Backend.Stock.MemorySretCopy
set_option autoImplicit false

/-- Use the original sret copy class with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryCapturedCopy.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock sret memory candidate failed ABI-aware semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryCapturedCopy.lowerValidated f

/-- Keep published routes0–19 and append the sret provider as20. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryCapturedCopy.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemorySretCopy
