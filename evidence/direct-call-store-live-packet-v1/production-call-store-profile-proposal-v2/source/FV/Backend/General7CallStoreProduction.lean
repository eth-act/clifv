import FV.Backend.Lowering.StockGeneral7CallResultsNI
import FV.Backend.Lowering.StockCallStoreWith
import FV.Backend.ReturnPinProfileFile
import FV.Backend.ReturnPinProduction

namespace Backend.Stock.GeneralLoopCfg7.CallStoreNI
set_option autoImplicit false

def lowerValidated (f : Clif.Function) : Except String VCode :=
  CallStore.lowerWithPrevious CallResultNI.lowerValidated f

def lowerRoutes : List (Clif.Function → Except String VCode) := NI.lowerRoutes

def lowerWithRoutes (choices : List (String × Nat)) (f : Clif.Function) : Except String VCode :=
  RoutesWith.lowerWithRoutes CallStore.lowerWithPrevious CallResultNI.lowerValidated
    NI.lowerWithRoutes choices f

theorem lowerWithRoutes_explicit {choices : List (String × Nat)} {f : Clif.Function} {index : Nat}
    (selected : choices.lookup f.name = some index) :
    lowerWithRoutes choices f = NI.lowerWithRoutes choices f :=
  RoutesWith.lowerWithRoutes_explicit CallStore.lowerWithPrevious CallResultNI.lowerValidated
    NI.lowerWithRoutes selected

theorem previous_accepts {f : Clif.Function} {vc : VCode}
    (accepted : NI.lowerValidated f = .ok vc) : ∃ next, lowerValidated f = .ok next := by
  obtain ⟨middle,acceptedMiddle⟩ := CallResultNI.previous_accepts accepted
  exact CallStore.lowerWithPrevious_accepts acceptedMiddle

theorem previous_stock_exact {f : Clif.Function} {result : Stock.Result}
    (lowered : Stock.lower f = .ok result) (accepted : NI.lowerValidated f = .ok result.code) :
    lowerValidated f = .ok result.code :=
  CallStore.lowerWithPrevious_preserves lowered (CallResultNI.previous_stock_exact lowered accepted)

end Backend.Stock.GeneralLoopCfg7.CallStoreNI

namespace Backend
set_option autoImplicit false

/-- Every rejection retries the complete current file action with its original callback and settings. -/
def compileFileGeneral7CallStoreWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String) := []) (cleanup : Bool := true) : m FileAsm :=
  ReturnPinProfileFile.compileFileWhen enabled (fun _ => true)
    Stock.GeneralLoopCfg7.CallStoreNI.lowerValidated SemanticABI.checkCallStores
    "Stock call-store profile failed internal semantic admission" alloc pf pre cleanup
    (compileFileReturnPinWhen enabled alloc pf pre cleanup)

theorem compileFileGeneral7CallStoreWhen_disabled {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) :
    compileFileGeneral7CallStoreWhen false alloc pf pre cleanup =
      compileFileReturnPinWhen false alloc pf pre cleanup :=
  ReturnPinProfileFile.compileFileWhen_disabled _ _ _ _ _ _ _ _ _

end Backend
