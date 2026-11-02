import FV.Backend.ConditionalForwardCfgNIProduction
import FV.Backend.Lowering.StockParameterCfgNI

namespace Backend
set_option autoImplicit false

def lowerCheckedParameterCfgNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.ParameterCfg.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired CFG semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedConditionalForwardCfgNI f verify

def lowerForAllocationParameterCfgNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedParameterCfgNI f verify).map (Stock.Arithmetic.stage cleanup)

/-- Retry the previous complete CFG pipeline with the original input,
allocator and settings if any new CFG attempt is unsupported or fails layout. -/
def compileFileParameterCfgNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileConditionalForwardCfgNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.ParameterCfg.leafEligible) then
    return ← compileFileConditionalForwardCfgNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationParameterCfgNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileConditionalForwardCfgNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
