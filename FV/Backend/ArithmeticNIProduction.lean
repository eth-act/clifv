import FV.Backend.ScalarProduction
import FV.Backend.Lowering.StockArithmeticNI
import FV.Backend.StockArithmeticStageF

namespace Backend
set_option autoImplicit false

/-- The complete paired semantic checker validates actual selected code before
it can reach a verified allocation. Failure retries the shipped lowerer. -/
def lowerCheckedArithmeticNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.Arithmetic.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedProductionWith Stock.ScalarAdd.lower f verify

def lowerForAllocationArithmeticNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedArithmeticNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- One complete transactional file attempt, using the same source, allocator,
verification and cleanup settings. Earlier shipped classes keep their selectors. -/
def compileFileArithmeticNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileScalarWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.Arithmetic.eligible) then
    return ← compileFileScalarWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationArithmeticNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileScalarWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
