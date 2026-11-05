import FV.Backend.ScalarProduction
import FV.Backend.StockArithmeticCheck
import FV.Backend.StockArithmeticStageF

namespace Backend
set_option autoImplicit false

/-- A semantic-checker-aware attempt, retaining the shipped scalar/D0/prologue
route on failure. Verification is applied to the actual selected output. -/
def lowerCheckedSemanticWith (lower : Clif.Function → Except String VCode)
    (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← lower f
    if verify && !Stock.Arithmetic.check f vc then
      throw "lowering rejected by the semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedProductionWith Stock.ScalarAdd.lower f verify

def lowerForAllocationArithmetic (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedSemanticWith Stock.Arithmetic.lowerCandidate f verify).map
    (Stock.Arithmetic.stageV verify cleanup f)

/-- Arithmetic candidates use the same allocator, cleanup setting and emission
pipeline as the shipped compiler. Any function or layout failure retries the
previous complete production pipeline before an artifact is published. -/
def compileFileArithmeticWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileScalarWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.Arithmetic.eligible) then
    return ← compileFileScalarWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationArithmetic VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileScalarWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
