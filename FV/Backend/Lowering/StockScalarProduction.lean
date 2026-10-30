import FV.Backend.Lowering.StockPrologueAll
import FV.Backend.Lowering.StockScalarAdd

/-! Additive scalar-add selection. The earlier D0/prologue selectors keep their
meaning and remain the fallback for every other input or failed attempt. -/
set_option autoImplicit false
namespace Backend.Stock.ScalarAdd

def lowerWith (stock : Clif.Function → Except String Result) (f : Clif.Function) : Except String VCode :=
  if eligible f then
    match stock f with
    | .ok r =>
      if r.edgeArgs.all (fun row => row.all (·.isEmpty)) then .ok (D0.compact f.name r)
      else Prologue.AllConfigurations.lower f
    | .error _ => Prologue.AllConfigurations.lower f
  else Prologue.AllConfigurations.lower f

def lower (f : Clif.Function) : Except String VCode := lowerWith Stock.lower f

def activationEligible (f : Clif.Function) : Bool := eligible f || Prologue.AllConfigurations.eligible f
end Backend.Stock.ScalarAdd
