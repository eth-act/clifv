import FV.Backend.ProductionWith
import FV.Backend.Lowering.StockScalarProduction

/-! Monotone rollout of the complete scalar-add class alongside the shipped
prologue and D0 routes, with the original whole-file retry on any failure. -/
set_option autoImplicit false
namespace Backend

def compileFileScalarWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm :=
  if enabled then compileFileProductionWith Stock.ScalarAdd.lower Stock.ScalarAdd.activationEligible
    alloc pf preUnverified cleanup
  else compileFileWith alloc pf preUnverified cleanup
end Backend
