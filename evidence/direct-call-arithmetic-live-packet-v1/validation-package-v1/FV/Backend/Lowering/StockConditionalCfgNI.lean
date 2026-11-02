import FV.Backend.Lowering.StockForwardCfgNI
import FV.Backend.Lowering.StockConditionalCfg

namespace Backend.Stock.ConditionalCfg
set_option autoImplicit false

/-- The compatible conditional CFG is checked before publication. Every failure uses
exactly the previous complete CFG provider on the original function. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !leafEligible f then ForwardCfg.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock conditional candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => ForwardCfg.lowerValidated f

/-- Previously published artifact indices0–8 remain unchanged. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  ForwardCfg.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.ConditionalCfg
