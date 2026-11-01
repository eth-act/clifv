import FV.Backend.MemoryStoreNIProduction
import FV.Backend.Lowering.StockMemoryStoreCfgNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryStoreCfgNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemoryStoreCfg.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired store memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryStoreNI f verify

def lowerForAllocationMemoryStoreCfgNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryStoreCfgNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete pipeline on the original input and allocation
callback if store selection, allocation, emission or layout fails. -/
def compileFileMemoryStoreCfgNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryStoreNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemoryStoreCfg.eligible) then
    return ← compileFileMemoryStoreNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryStoreCfgNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryStoreNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
