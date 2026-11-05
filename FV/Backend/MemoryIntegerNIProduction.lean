import FV.Backend.MemoryCfgNIProduction
import FV.Backend.Lowering.StockMemoryIntegerNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryIntegerNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemoryUnsigned.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired unsigned memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryCfgNI f verify

def lowerForAllocationMemoryIntegerNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryIntegerNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete pipeline on the original input and allocation
callback if unsigned selection, allocation, emission or layout fails. -/
def compileFileMemoryIntegerNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryCfgNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemoryUnsigned.eligible) then
    return ← compileFileMemoryCfgNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryIntegerNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryCfgNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
