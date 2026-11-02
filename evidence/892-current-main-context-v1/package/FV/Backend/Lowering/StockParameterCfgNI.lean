import FV.Backend.Lowering.StockConditionalForwardCfgNI
import FV.Backend.Lowering.StockParameterCfg

namespace Backend.Stock.ParameterCfg
set_option autoImplicit false

/-- The compatible ranked parameter-conditional CFG is checked before publication. Every failure uses
exactly the previous complete CFG provider on the original function. -/
def eligible (f : Clif.Function) : Bool :=
  sourceEligible f && hasNonentryConditional f

/-- The same class when nonentry blocks may also end in `trap`. -/
def leafEligible (f : Clif.Function) : Bool :=
  sourceLeafEligible f && hasNonentryConditional f

def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !leafEligible f then ConditionalForwardCfg.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock conditional candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => ConditionalForwardCfg.lowerValidated f

/-- Previously published artifact indices0–10 remain unchanged. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  ConditionalForwardCfg.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.ParameterCfg
