import FV.Backend.Lowering.StockCheckedRoutesWith
import FV.Backend.Lowering.StockResultCallWith
import FV.Backend.Lowering.StockLiveCallWith

namespace Backend.Stock.CallResultExtensions
set_option autoImplicit false

/-- The complete supplied predecessor remains after both proved call-result classes. -/
def lowerValidatedWith (previous : Clif.Function → Except String VCode)
    (f : Clif.Function) : Except String VCode :=
  LiveCall.lowerWithPrevious (ResultCall.lowerWithPrevious previous) f

def lowerWithRoutesWith (previous : Clif.Function → Except String VCode)
    (previousRoutes : List (String × Nat) → Clif.Function → Except String VCode)
    (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  RoutesWith.lowerWithRoutes lowerValidatedWith previous previousRoutes choices f

theorem lowerWithRoutesWith_explicit
    (previous : Clif.Function → Except String VCode)
    (previousRoutes : List (String × Nat) → Clif.Function → Except String VCode)
    {choices : List (String × Nat)} {f : Clif.Function} {index : Nat}
    (selected : choices.lookup f.name = some index) :
    lowerWithRoutesWith previous previousRoutes choices f = previousRoutes choices f :=
  RoutesWith.lowerWithRoutes_explicit lowerValidatedWith previous previousRoutes selected

theorem lowerWithRoutesWith_default
    (previous : Clif.Function → Except String VCode)
    (previousRoutes : List (String × Nat) → Clif.Function → Except String VCode)
    {choices : List (String × Nat)} {f : Clif.Function}
    (selected : choices.lookup f.name = none) :
    lowerWithRoutesWith previous previousRoutes choices f = lowerValidatedWith previous f :=
  RoutesWith.lowerWithRoutes_default lowerValidatedWith previous previousRoutes selected

theorem lowerValidatedWith_preserves
    {previous : Clif.Function → Except String VCode} {f : Clif.Function} {result : Stock.Result}
    (lowered : Stock.lower f = .ok result) (accepted : previous f = .ok result.code) :
    lowerValidatedWith previous f = .ok result.code :=
  LiveCall.lowerWithPrevious_preserves lowered
    (ResultCall.lowerWithPrevious_preserves lowered accepted)

/-- Complete retry retains every accepted predecessor input. -/
theorem lowerValidatedWith_accepts
    {previous : Clif.Function → Except String VCode} {f : Clif.Function} {vc : VCode}
    (accepted : previous f = .ok vc) :
    ∃ next, lowerValidatedWith previous f = .ok next := by
  obtain ⟨middle, acceptedMiddle⟩ := ResultCall.lowerWithPrevious_accepts accepted
  exact LiveCall.lowerWithPrevious_accepts acceptedMiddle

end Backend.Stock.CallResultExtensions
