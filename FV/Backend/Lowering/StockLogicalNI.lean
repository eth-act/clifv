import FV.Backend.Lowering.StockMixedNI
import FV.Backend.StockLogicalCheck

namespace Backend.Stock.Logical
set_option autoImplicit false

/-- A complete new candidate is checked before consumers see it. Every other
input or failed candidate retains the previous mixed production route. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !activationEligible f then Mixed.lowerValidated f
  else
    let attempt := do
      let vc ← lowerCandidate f
      if check f vc && ABIReadFlags.check f.sig vc then pure vc
      else throw "Stock logical candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => Mixed.lowerValidated f

/-- Retained-artifact reconstruction is selected from actual artifact checks;
names carry routing data and never restrict the proved source class. -/
def lowerWithFallbacks (retained : List String) (f : Clif.Function) : Except String VCode :=
  if retained.contains f.name then Mixed.lowerWithFallbacks retained f
  else lowerValidated f

end Backend.Stock.Logical
