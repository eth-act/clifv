import FV.Backend.Lowering.StockLogicalNI
import FV.Backend.StockScalarCheck
import FV.Backend.ABIReadScalar

namespace Backend.Stock.Scalar
set_option autoImplicit false

/-- A complete new candidate is checked before consumers see it. Every other
input or failed candidate retains the previous logical production route. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !activationEligible f then Logical.lowerValidated f
  else
    let attempt := do
      let vc ← lowerCandidate f
      if check f vc && ABIReadScalar.check f.sig vc then pure vc
      else throw "Stock scalar candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => Logical.lowerValidated f

/-- Retained-artifact reconstruction is selected from actual artifact checks;
names carry routing data and never restrict the proved source class. -/
def lowerWithFallbacks (retained : List String) (f : Clif.Function) : Except String VCode :=
  if retained.contains f.name then Logical.lowerWithFallbacks retained f
  else lowerValidated f

/-- Actual artifact reconstruction can retain any earlier complete lowering
route. These names/indices are data; semantic and binary checks validate the
selected artifact. Later scalar families reuse this same consumer interface. -/
def lowerRoutes : List (Clif.Function → Except String VCode) :=
  [lowerValidated,Logical.lowerValidated,Mixed.lowerValidated,Arithmetic.lowerValidated,ScalarAdd.lower]

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  ((lowerRoutes[(choices.lookup f.name).getD 0]?).getD ScalarAdd.lower) f

end Backend.Stock.Scalar
