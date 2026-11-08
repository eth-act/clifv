import FV.Backend.Lowering.StockMemoryCapturedCopyNI
import FV.Backend.StockMemorySinkExtCheck

namespace Backend.Stock.MemorySinkExt
set_option autoImplicit false

/-- Add the sinking load/extension functions with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryCapturedCopy.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock sinking load/extension candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryCapturedCopy.lowerValidated f

/-- Keep published routes0–19 and append the sinking provider as20. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryCapturedCopy.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemorySinkExt
