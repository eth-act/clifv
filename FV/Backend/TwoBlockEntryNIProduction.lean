import FV.Backend.TwoBlockNIProduction
import FV.Backend.Lowering.StockTwoBlockEntryNI

namespace Backend
set_option autoImplicit false

def lowerCheckedTwoBlockEntryNI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.TwoBlock.Entry.lowerValidated f
    if verify && !SemanticNI.check f vc then
      throw "lowering rejected by the paired CFG semantic lowering validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedTwoBlockNI f verify

def lowerForAllocationTwoBlockEntryNI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedTwoBlockEntryNI f verify).map (Stock.Arithmetic.stageV verify cleanup f)

/-- Retry the previous complete CFG pipeline with the original input,
allocator and settings if any new CFG attempt is unsupported or fails layout. -/
def compileFileTwoBlockEntryNIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileTwoBlockNIWhen false alloc pf preUnverified cleanup
  if !(pf.funcs.any fun p => p.func.toOption.any Stock.TwoBlock.Entry.eligible) then
    return ← compileFileTwoBlockNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationTwoBlockEntryNI VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileTwoBlockNIWhen true alloc pf preUnverified cleanup
  else pure attempt

end Backend
