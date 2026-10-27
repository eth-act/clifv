import FV.Backend.ArithmeticNIProduction
import FV.Backend.Lowering.StockMixedNI

namespace Backend
set_option autoImplicit false

def lowerCheckedMixedNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.Mixed.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedArithmeticNI f verify

def lowerForAllocationMixedNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedMixedNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- A failed complete attempt retries the previous complete arithmetic pipeline
with the original source, allocator and verification/cleanup settings. -/
def compileFileMixedNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileArithmeticNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.Mixed.activationEligible) then
    return ← compileFileArithmeticNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationMixedNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileArithmeticNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
