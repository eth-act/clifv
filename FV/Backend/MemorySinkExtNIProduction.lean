import FV.Backend.MemoryCapturedCopyNIProduction
import FV.Backend.Lowering.StockMemorySinkExtNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemorySinkExtNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemorySinkExt.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired sinking memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryCapturedCopyNI f verify

def lowerForAllocationMemorySinkExtNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemorySinkExtNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the complete previous pipeline with the original input and allocation callback. -/
def compileFileMemorySinkExtNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryCapturedCopyNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemorySinkExt.eligible) then
    return ← compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemorySinkExtNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
