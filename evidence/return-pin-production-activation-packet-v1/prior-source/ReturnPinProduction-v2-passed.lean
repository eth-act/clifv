import FV.Backend.VoidCallABIProduction

namespace Backend
set_option autoImplicit false

/-- Check the actual artifacts against the program theorem's semantic admission rule. -/
def returnPinModeB (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool) : Bool :=
  (ReturnPinFile.entries pf pre cleanup).toOption.any fun entries =>
    entries.all fun e => SemanticABI.checkCalls e.source e.raw

/-- A rejected mode runs the complete previous action with the original allocator. -/
def compileFileReturnPinWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String) := []) (cleanup : Bool := true) : m FileAsm :=
  if enabled && !returnPinModeB pf pre cleanup then
    compileFileMemoryCapturedCopyNIWhen enabled alloc pf pre cleanup
  else compileFileVoidCallABIWhen enabled alloc pf pre cleanup

theorem compileFileReturnPinWhen_retry {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool)
    (rejected : returnPinModeB pf pre cleanup = false) :
    compileFileReturnPinWhen true alloc pf pre cleanup =
      compileFileMemoryCapturedCopyNIWhen true alloc pf pre cleanup := by
  simp only [compileFileReturnPinWhen,rejected,Bool.not_false,Bool.true_and,ite_true]

theorem compileFileReturnPinWhen_admitted {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool)
    (accepted : returnPinModeB pf pre cleanup = true) :
    compileFileReturnPinWhen true alloc pf pre cleanup =
      compileFileVoidCallABIWhen true alloc pf pre cleanup := by
  simp only [compileFileReturnPinWhen,accepted,Bool.not_true,Bool.true_and,Bool.false_eq_true,ite_false]

theorem compileFileReturnPinWhen_disabled {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) :
    compileFileReturnPinWhen false alloc pf pre cleanup =
      compileFileMemoryCapturedCopyNIWhen false alloc pf pre cleanup := by
  simp only [compileFileReturnPinWhen,Bool.false_and,Bool.false_eq_true,ite_false,
    compileFileVoidCallABIWhen,Bool.not_false,ite_true]

end Backend
