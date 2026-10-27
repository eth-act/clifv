import FV.Backend.MixedNIProduction
import FV.Backend.Lowering.StockLogicalNI

namespace Backend
set_option autoImplicit false

def lowerCheckedLogicalNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.Logical.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMixedNI f verify

def lowerForAllocationLogicalNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedLogicalNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- A failed complete attempt retries the previous complete mixed pipeline
with the original source, allocator and verification/cleanup settings. -/
def compileFileLogicalNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMixedNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.Logical.activationEligible) then
    return ← compileFileMixedNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationLogicalNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileMixedNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
