import FV.Backend.Lowering.StockGeneralLoopCfg7NI
import FV.Backend.Lowering.StockCallResultExtensionsWith

namespace Backend.Stock.GeneralLoopCfg7.CallResultNI
set_option autoImplicit false

/-- Extend the complete General7 default without changing its explicit routes. -/
def lowerValidated (f : Clif.Function) : Except String VCode :=
  CallResultExtensions.lowerValidatedWith NI.lowerValidated f

def lowerRoutes : List (Clif.Function → Except String VCode) := NI.lowerRoutes

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) :
    Except String VCode :=
  CallResultExtensions.lowerWithRoutesWith NI.lowerValidated NI.lowerWithRoutes choices f

theorem lowerRoutes_exact : lowerRoutes = NI.lowerRoutes := rfl

theorem lowerWithRoutes_explicit {choices : List (String × Nat)} {f : Clif.Function}
    {index : Nat} (selected : choices.lookup f.name = some index) :
    lowerWithRoutes choices f = NI.lowerWithRoutes choices f :=
  CallResultExtensions.lowerWithRoutesWith_explicit NI.lowerValidated NI.lowerWithRoutes selected

theorem lowerWithRoutes_default {choices : List (String × Nat)} {f : Clif.Function}
    (selected : choices.lookup f.name = none) :
    lowerWithRoutes choices f = lowerValidated f :=
  CallResultExtensions.lowerWithRoutesWith_default NI.lowerValidated NI.lowerWithRoutes selected

/-- Every previous accepted function remains accepted after extending the default. -/
theorem previous_accepts {f : Clif.Function} {vc : VCode}
    (accepted : NI.lowerValidated f = .ok vc) :
    ∃ next, lowerValidated f = .ok next :=
  CallResultExtensions.lowerValidatedWith_accepts accepted

/-- An accepted previous Stock result keeps its exact code. -/
theorem previous_stock_exact {f : Clif.Function} {result : Stock.Result}
    (lowered : Stock.lower f = .ok result)
    (accepted : NI.lowerValidated f = .ok result.code) :
    lowerValidated f = .ok result.code :=
  CallResultExtensions.lowerValidatedWith_preserves lowered accepted

end Backend.Stock.GeneralLoopCfg7.CallResultNI
