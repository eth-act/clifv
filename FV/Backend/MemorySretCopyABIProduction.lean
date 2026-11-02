import FV.Backend.MemoryCapturedCopyNIProduction
import FV.Backend.SemanticABICheck
import FV.Backend.Lowering.StockMemorySretCopyNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemorySretCopyABI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemorySretCopy.lowerValidated f
    if verify && !SemanticABI.check f vc then
      throw "lowering rejected by the ABI-aware sret memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryCapturedCopyNI f verify

def lowerForAllocationMemorySretCopyABI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemorySretCopyABI f verify).map (Stock.Arithmetic.stage cleanup)

/-- Retry the complete previous pipeline with the original input and allocation callback. -/
def compileFileMemorySretCopyABIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryCapturedCopyNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemorySretCopy.eligible) then
    return ← compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemorySretCopyABI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
