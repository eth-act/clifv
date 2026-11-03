import FV.Backend.Lowering.StockCheckedWith

namespace Backend.Stock.RoutesWith
set_option autoImplicit false

/-- Only an absent explicit choice selects the extended default. -/
def lowerWithRoutes
    (extend : (Clif.Function → Except String VCode) → Clif.Function → Except String VCode)
    (previous : Clif.Function → Except String VCode)
    (previousRoutes : List (String × Nat) → Clif.Function → Except String VCode)
    (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  match choices.lookup f.name with
  | none => extend previous f
  | some _ => previousRoutes choices f

theorem lowerWithRoutes_explicit
    (extend : (Clif.Function → Except String VCode) → Clif.Function → Except String VCode)
    (previous : Clif.Function → Except String VCode)
    (previousRoutes : List (String × Nat) → Clif.Function → Except String VCode)
    {choices : List (String × Nat)} {f : Clif.Function} {index : Nat}
    (selected : choices.lookup f.name = some index) :
    lowerWithRoutes extend previous previousRoutes choices f = previousRoutes choices f := by
  simp only [lowerWithRoutes,selected]

theorem lowerWithRoutes_default
    (extend : (Clif.Function → Except String VCode) → Clif.Function → Except String VCode)
    (previous : Clif.Function → Except String VCode)
    (previousRoutes : List (String × Nat) → Clif.Function → Except String VCode)
    {choices : List (String × Nat)} {f : Clif.Function}
    (selected : choices.lookup f.name = none) :
    lowerWithRoutes extend previous previousRoutes choices f = extend previous f := by
  simp only [lowerWithRoutes,selected]

end Backend.Stock.RoutesWith
