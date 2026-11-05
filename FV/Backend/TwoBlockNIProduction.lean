import FV.Backend.ScalarNIProduction
import FV.Backend.Lowering.StockTwoBlockNI

namespace Backend
set_option autoImplicit false

def lowerCheckedTwoBlockNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.TwoBlock.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired CFG semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedScalarNI f verify

def lowerForAllocationTwoBlockNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedTwoBlockNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete production pipeline with the original input,
allocator and settings if any new CFG attempt is unsupported or fails layout. -/
def compileFileTwoBlockNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileScalarNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.TwoBlock.eligible) then
    return ← compileFileScalarNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationTwoBlockNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileScalarNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
