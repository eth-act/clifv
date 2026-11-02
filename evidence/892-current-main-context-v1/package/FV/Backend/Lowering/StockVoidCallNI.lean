import FV.Backend.Lowering.StockMemorySretCopyNI
import FV.Backend.StockVoidCallNICheck

namespace Backend.Stock.VoidCall.NI
set_option autoImplicit false

/-- Admit the proved caller class and retain the complete previous provider on rejection. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if (Stock.VoidCall.sourceData? f).isNone then MemorySretCopy.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock void caller failed source and paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemorySretCopy.lowerValidated f

/-- Retain all published routes and append the checked caller provider as route21. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemorySretCopy.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.VoidCall.NI
