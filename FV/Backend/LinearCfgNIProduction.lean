import FV.Backend.TwoBlockEntryNIProduction
import FV.Backend.Lowering.StockLinearCfgNI

namespace Backend
set_option autoImplicit false

def lowerCheckedLinearCfgNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.LinearCfg.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired CFG semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedTwoBlockEntryNI f verify

def lowerForAllocationLinearCfgNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedLinearCfgNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete CFG pipeline with the original input,
allocator and settings if any new CFG attempt is unsupported or fails layout. -/
def compileFileLinearCfgNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileTwoBlockEntryNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.LinearCfg.eligible) then
    return ← compileFileTwoBlockEntryNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationLinearCfgNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileTwoBlockEntryNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
