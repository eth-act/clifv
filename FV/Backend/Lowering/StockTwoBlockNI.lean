module

public import FV.Backend.Lowering.StockScalarNI
import FV.Backend.Lowering.StockTwoBlock
import FV.Backend.ABIReadCfg

@[expose] public section

namespace Backend.Stock.TwoBlock
set_option autoImplicit false

/-- Validate the complete CFG candidate, including actual entry-read control
flow. Every failed candidate retains the previous scalar production route. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !eligible f then Scalar.lowerValidated f
  else
    let attempt := do
      let result ← Stock.lower f
      if check f result.code && ABIReadCfg.check f.sig result.code then pure result.code
      else throw "Stock two-block candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => Scalar.lowerValidated f

/-- Old retained indices retain their meanings; the new complete route is
appended for byte-based reconstruction of newly compiled CFG artifacts. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  Scalar.lowerRoutes ++ [lowerValidated]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some index => ((lowerRoutes[index]?).getD ScalarAdd.lower) f

end Backend.Stock.TwoBlock
