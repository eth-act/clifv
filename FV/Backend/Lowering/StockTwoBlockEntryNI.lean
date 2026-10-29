module

public import FV.Backend.Lowering.StockTwoBlockNI
import FV.Backend.Lowering.StockTwoBlockEntry

@[expose] public section

namespace Backend.Stock.TwoBlock.Entry
set_option autoImplicit false

/-- The broader entry body is checked before publication. Every failure uses
exactly the previous complete CFG provider on the original function. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then TwoBlock.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock entry-body candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => TwoBlock.lowerValidated f

/-- Previously published artifact indices0–5 remain unchanged. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  TwoBlock.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.TwoBlock.Entry
