import FV.Backend.Lowering.StockProduction

/-! The six-configuration extension is additive: the published SystemV selector
and all of its theorem interfaces retain their meaning. -/
set_option autoImplicit false
namespace Backend.Stock.Prologue.AllConfigurations
open D0

def eligible (f : Clif.Function) : Bool :=
  configurations.any fun c => decide (f = Prologue.source f.name c f.runs)

def lowerWith (stock : Clif.Function → Except String Result) (f : Clif.Function) :
    Except String VCode :=
  if eligible f then
    match stock f with
    | .ok r =>
      if r.edgeArgs.all (fun row => row.all (·.isEmpty)) then .ok (compact f.name r)
      else Production.lower f
    | .error _ => Production.lower f
  else Production.lower f

def lower (f : Clif.Function) : Except String VCode := lowerWith Stock.lower f
end Backend.Stock.Prologue.AllConfigurations
