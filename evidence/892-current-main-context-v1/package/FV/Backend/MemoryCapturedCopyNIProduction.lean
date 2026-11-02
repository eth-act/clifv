import FV.Backend.MemoryLoadStoreNIProduction
import FV.Backend.Lowering.StockMemoryCapturedCopyNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryCapturedCopyNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemoryCapturedCopy.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired captured memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryLoadStoreNI f verify

def lowerForAllocationMemoryCapturedCopyNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryCapturedCopyNI f verify).map (Stock.Arithmetic.stage cleanup)

/-- Retry the complete previous pipeline with the original input and allocation callback. -/
def compileFileMemoryCapturedCopyNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryLoadStoreNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemoryCapturedCopy.eligible) then
    return ← compileFileMemoryLoadStoreNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryCapturedCopyNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryLoadStoreNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
