module

public import FV.Backend.Lowering.StockMixed
public import FV.Backend.StockArithmeticCheck

public section

namespace Backend.Stock.Mixed
open Backend.Proof.Driver
set_option autoImplicit false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- Only the new actual-Stock branch; the production union retains its previous
legacy/arithmetic alternatives and transactional fallbacks. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && result.edgeArgs.all (fun row => row.all (·.isEmpty))


end Backend.Stock.Mixed
