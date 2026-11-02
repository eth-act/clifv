import FV.Backend.MemoryStoreCfgNIProduction
import FV.Backend.Lowering.StockMemoryLoadStoreNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryLoadStoreNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.MemoryLoadStore.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired mixed memory semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryStoreCfgNI f verify

def lowerForAllocationMemoryLoadStoreNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryLoadStoreNI f verify).map (Stock.Arithmetic.stage cleanup)

/-- Retry the complete previous pipeline with the original input and allocation callback. -/
def compileFileMemoryLoadStoreNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryStoreCfgNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.MemoryLoadStore.eligible) then
    return ← compileFileMemoryStoreCfgNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryLoadStoreNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMemoryStoreCfgNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
