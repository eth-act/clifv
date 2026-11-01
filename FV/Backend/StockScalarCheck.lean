import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.Scalar
open Backend.Proof.Driver
set_option autoImplicit false

def sourceOk (f : Clif.Function) : Bool :=
  (productionEligible f || maskTrapEligible f) && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- Actual source and Stock artifact checks. No runtime proof input. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && result.edgeArgs.all (fun row => row.all (·.isEmpty))

end Backend.Stock.Scalar
