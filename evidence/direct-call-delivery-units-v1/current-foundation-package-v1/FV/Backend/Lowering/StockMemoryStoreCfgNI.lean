import FV.Backend.Lowering.StockMemoryStoreNI
import FV.Backend.StockMemoryStoreCfgCheck

namespace Backend.Stock.MemoryStoreCfg
set_option autoImplicit false

/-- Add the proved integer-store CFG class with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryStore.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock store memory candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryStore.lowerValidated f

/-- Keep published routes0–16 and append the store provider as17. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryStore.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemoryStoreCfg
