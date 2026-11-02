import FV.Backend.Lowering.StockLiveCallWith
import FV.Backend.Lowering.StockResultCallRoutes

namespace Backend.Stock.LiveCall
set_option autoImplicit false

/-- Keep the complete preceding default and every old explicit route. -/
def lowerValidated : Clif.Function → Except String VCode := lowerWithPrevious ResultCall.lowerValidated

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some _ => ResultCall.lowerWithRoutes choices f

theorem lowerWithRoutes_default {choices : List (String × Nat)} {f : Clif.Function}
    (absent : choices.lookup f.name = none) : lowerWithRoutes choices f = lowerValidated f := by
  simp only [lowerWithRoutes,absent]

theorem lowerWithRoutes_explicit {choices : List (String × Nat)} {f : Clif.Function} {index : Nat}
    (chosen : choices.lookup f.name = some index) :
    lowerWithRoutes choices f = ResultCall.lowerWithRoutes choices f := by
  simp only [lowerWithRoutes,chosen]

end Backend.Stock.LiveCall
