import FV.Backend.Lowering.StockResultCallWith
import FV.Backend.Lowering.StockVoidCallNI

namespace Backend.Stock.ResultCall
set_option autoImplicit false

/-- The agreed production default retains the complete route22 provider as fallback. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  lowerWithPrevious VoidCall.NI.lowerValidated f

/-- Old explicit indices keep their exact providers; an absent choice uses the new default. -/
def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => lowerValidated f
  | some _ => VoidCall.NI.lowerWithRoutes choices f

theorem lowerWithRoutes_explicit {choices : List (String × Nat)} {f : Clif.Function} {index : Nat}
    (selected : choices.lookup f.name = some index) :
    lowerWithRoutes choices f = VoidCall.NI.lowerWithRoutes choices f := by
  simp only [lowerWithRoutes,selected]

theorem lowerWithRoutes_default {choices : List (String × Nat)} {f : Clif.Function}
    (selected : choices.lookup f.name = none) : lowerWithRoutes choices f = lowerValidated f := by
  simp only [lowerWithRoutes,selected]

end Backend.Stock.ResultCall
