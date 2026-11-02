import FV.Backend.Lowering.StockMemoryStoreCfgNI
import FV.Backend.StockMemoryLoadStoreCheck

namespace Backend.Stock.MemoryLoadStore
set_option autoImplicit false

/-- Add complete mixed load/store functions with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryStoreCfg.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock mixed memory candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryStoreCfg.lowerValidated f

/-- Preserve published routes0–17 and append the mixed provider as18. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryStoreCfg.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemoryLoadStore
