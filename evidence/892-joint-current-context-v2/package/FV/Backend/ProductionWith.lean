import FV.Backend
import FV.Backend.Lowering.StockPrologueAll

/-! Shared transactional orchestration for successive proved lowering classes. -/
set_option autoImplicit false
namespace Backend
-- The runtime adapter accepts only data/functions, never a correctness certificate.
def lowerCheckedProductionWith (lower : Clif.Function → Except String VCode)
    (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← lower f
    if verify && !Proof.Driver.lowerCheck f vc then
      throw "lowering rejected by the M7 lowering validator (lowerCheck)"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerChecked f verify

def lowerForAllocationProductionWith (lower : Clif.Function → Except String VCode)
    (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedProductionWith lower f verify).map fun vc => if cleanup then DeadCleanup.prune vc else vc

def compileFileProductionWith {m : Type → Type} [Monad m]
    (lower : Clif.Function → Except String VCode) (eligible : Clif.Function → Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !(pf.funcs.any fun p => p.func.toOption.any eligible) then
    return ← compileFileWith alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering (lowerForAllocationProductionWith lower) VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileWith alloc pf preUnverified cleanup
  else pure attempt

def compileFilePrologueAllWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm :=
  if enabled then compileFileProductionWith Stock.Prologue.AllConfigurations.lower
    Stock.Prologue.AllConfigurations.eligible alloc pf preUnverified cleanup
  else compileFileWith alloc pf preUnverified cleanup
end Backend
