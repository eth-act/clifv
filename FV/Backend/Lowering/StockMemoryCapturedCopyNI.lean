import FV.Backend.Lowering.StockMemoryLoadStoreNI
import FV.Backend.StockMemoryCapturedCopyCheck

namespace Backend.Stock.MemoryCapturedCopy
set_option autoImplicit false

/-- Add complete captured memory-copy functions with the complete previous provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then MemoryLoadStore.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code then pure result.code
      else throw "Stock captured memory candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => MemoryLoadStore.lowerValidated f

/-- Preserve published routes0–18 and append the mixed provider as19. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  MemoryLoadStore.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.MemoryCapturedCopy
