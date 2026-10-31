import FV.Backend.MemoryIntegerNIProduction
import FV.Backend.Lowering.StockMemoryExtLoadNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryExtLoadNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemoryExtending.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired extending memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryIntegerNI f verify

def lowerForAllocationMemoryExtLoadNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryExtLoadNI f verify).map (Stock.Arithmetic.stage cleanup)

/-- Retry the previous complete pipeline on the original input and allocation
callback if extending selection, allocation, emission or layout fails. -/
def compileFileMemoryExtLoadNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryIntegerNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemoryExtending.eligible) then
    return ← compileFileMemoryIntegerNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryExtLoadNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryIntegerNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
