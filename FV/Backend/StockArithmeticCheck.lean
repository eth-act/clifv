module

public import FV.Backend.Lowering.StockArithmetic
public import FV.Backend.Proof.LowerDecide

@[expose] public section

namespace Backend.Stock.Arithmetic
open Backend.Proof.Driver
set_option autoImplicit false

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode

/-- Source-only conditions for the new semantic route. Other inputs retain
the existing compiler route; these conditions are not a global admission test. -/
def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- Validate actual Stock provenance as well as the source class. Existing
lowering verdicts keep their meaning and remain accepted. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  lowerCheck f vc || (sourceOk f &&
    match Stock.lower f with
    | .error _ => false
    | .ok result => decide (result.code = vc) &&
        result.edgeArgs.all (fun row => row.all (·.isEmpty)))

end Backend.Stock.Arithmetic
