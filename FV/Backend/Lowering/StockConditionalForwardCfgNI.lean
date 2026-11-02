import FV.Backend.Lowering.StockConditionalCfgNI
import FV.Backend.Lowering.StockConditionalRankedCfg

namespace Backend.Stock.ConditionalForwardCfg
set_option autoImplicit false

/-- The compatible conditional CFG with forward tails is checked before publication. Every failure uses
exactly the previous complete CFG provider on the original function. -/
def eligible (f : Clif.Function) : Bool :=
  ConditionalCfg.rankedEligible f && !ConditionalCfg.eligible f

/-- The same split when leaf blocks may also end in `trap`. -/
def leafEligible (f : Clif.Function) : Bool :=
  ConditionalCfg.rankedLeafEligible f && !ConditionalCfg.leafEligible f

def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !leafEligible f then ConditionalCfg.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if ConditionalCfg.rankedCheck f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock conditional candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => ConditionalCfg.lowerValidated f

/-- Previously published artifact indices0–9 remain unchanged. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  ConditionalCfg.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.ConditionalForwardCfg
