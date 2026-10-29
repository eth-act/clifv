module

public import FV.Backend.SemanticNICheck

@[expose] public section

namespace Backend.Stock.Arithmetic
set_option autoImplicit false

/-- One shared executable choice for compiler, checker, linker and generated
proofs. A candidate rejected by paired semantic validation retries the shipped
selector before any later stage observes code or rule history. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  if D0.eligible f || ScalarAdd.activationEligible f || !eligible f then ScalarAdd.lower f
  else
    let attempt := do
      let vc ← lowerCandidate f
      if SemanticNI.check f vc then pure vc
      else throw "Stock candidate failed paired semantic validation"
    match attempt with
    | .ok vc => .ok vc
    | .error _ => ScalarAdd.lower f


/-- Consumer routing data records retained artifacts discovered in a mixed
executable. It carries no proof: the ordinary semantic/allocation/binary checks
validate either selected route. No function name restricts the proved class. -/
def lowerWithFallbacks (retained : List String) (f : Clif.Function) : Except String VCode :=
  if retained.contains f.name then ScalarAdd.lower f else lowerValidated f

end Backend.Stock.Arithmetic
