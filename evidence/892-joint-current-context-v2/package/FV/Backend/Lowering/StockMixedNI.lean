import FV.Backend.Lowering.StockArithmeticNI

namespace Backend.Stock.Mixed
set_option autoImplicit false

/-- A complete new candidate is checked before consumers see it. Every other
input or failed candidate retains the previous arithmetic production route. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if !activationEligible f then Arithmetic.lowerValidated f
  else
    let attempt := do
      let vc ← lowerCandidate f
      if check f vc && ABIReadFlags.check f.sig vc then pure vc
      else throw "Stock mixed candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => Arithmetic.lowerValidated f

/-- Retained-artifact reconstruction is selected from actual artifact checks;
names carry routing data and never restrict the proved source class. -/
def lowerWithFallbacks (retained : List String) (f : Clif.Function) : Except String VCode :=
  if retained.contains f.name then Arithmetic.lowerWithFallbacks retained f
  else lowerValidated f

end Backend.Stock.Mixed
