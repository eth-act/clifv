import FV.Backend.MemoryExtLoadNIProduction
import FV.Backend.Lowering.StockMemoryStoreNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryStoreNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemoryStore.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired store memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryExtLoadNI f verify

def lowerForAllocationMemoryStoreNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryStoreNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete pipeline on the original input and allocation
callback if store selection, allocation, emission or layout fails. -/
def compileFileMemoryStoreNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryExtLoadNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemoryStore.eligible) then
    return ← compileFileMemoryExtLoadNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryStoreNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryExtLoadNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
