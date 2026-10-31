import FV.Backend.LinearCfgNIProduction
import FV.Backend.Lowering.StockForwardCfgNI

namespace Backend
set_option autoImplicit false

def lowerCheckedForwardCfgNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.ForwardCfg.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired CFG semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedLinearCfgNI f verify

def lowerForAllocationForwardCfgNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedForwardCfgNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete CFG pipeline with the original input,
allocator and settings if any new CFG attempt is unsupported or fails layout. -/
def compileFileForwardCfgNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileLinearCfgNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.ForwardCfg.eligible) then
    return ← compileFileLinearCfgNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationForwardCfgNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileLinearCfgNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
