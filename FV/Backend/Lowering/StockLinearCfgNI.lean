module

public import FV.Backend.Lowering.StockTwoBlockEntryNI
public import FV.Backend.Lowering.StockLinearCfg

@[expose] public section

namespace Backend.Stock.LinearCfg
set_option autoImplicit false

/-- The three-block scalar CFG is checked before publication. Every failure uses
exactly the previous complete CFG provider on the original function. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then TwoBlock.Entry.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock three-block candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => TwoBlock.Entry.lowerValidated f

/-- Previously published artifact indices0–6 remain unchanged. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  TwoBlock.Entry.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.LinearCfg
