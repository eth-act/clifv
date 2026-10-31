import FV.Backend.ParameterCfgNIProduction
import FV.Backend.Lowering.StockMemoryNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMemoryNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.Memory.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired CFG semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedParameterCfgNI f verify

def lowerForAllocationMemoryNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMemoryNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete CFG pipeline with the original input,
allocator and settings if any new CFG attempt is unsupported or fails layout. -/
def compileFileMemoryNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileParameterCfgNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.Memory.eligible) then
    return ← compileFileParameterCfgNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMemoryNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileParameterCfgNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
