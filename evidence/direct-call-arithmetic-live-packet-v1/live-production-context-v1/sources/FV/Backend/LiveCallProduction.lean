import FV.Backend.ResultCallProduction
import FV.Backend.Lowering.StockLiveCallRoutes

namespace Backend
set_option autoImplicit false

def lowerCheckedLiveCall (f : Clif.Function) (verify : Bool) : Except String VCode := do
  let raw ← Stock.LiveCall.lowerValidated f
  if verify && !SemanticABI.checkLiveCalls f raw then
    throw "lowering rejected by the proved live-call semantic validator"
  pure raw

def lowerForAllocationLiveCall (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedLiveCall f verify).map (Stock.Arithmetic.stage cleanup)

namespace LiveCallFile

def entry (f : Clif.Function) (verify cleanup : Bool) : Except String ReturnPinFile.Entry := do
  let raw ← lowerCheckedLiveCall f verify
  let prepared ← prepare (Stock.Arithmetic.stage cleanup raw)
  pure ⟨f,raw,prepared,Thunk.mk (fun _ => ReturnPinCheck.pins f raw),rfl⟩

def entries (pf : Clif.ParsedFile) (pre : List (String × String))
    (cleanup : Bool) : Except String (List ReturnPinFile.Entry) :=
  pf.funcs.mapM fun parsed => do
    let f ← parsed.func.mapError (fun error => error.toString)
    let verify := ((unverifiedReason? f).isSome || (pre.lookup parsed.name).isSome ||
      (overBudget? f).isSome).not
    entry f verify cleanup

/-- Derive whole-file compatibility from every actual raw artifact and its call metadata. -/
def modeB (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool) : Bool :=
  (entries pf pre cleanup).toOption.any fun actual =>
    actual.all (fun e => SemanticABI.checkLiveCalls e.source e.raw) && ReturnPinFile.check actual

end LiveCallFile

/-- Retain a complete live-call file or run the complete previous action with its original callback. -/
def compileFileLiveCallWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileResultCallWhen false alloc pf pre cleanup
  let relevant := pf.funcs.any fun parsed => parsed.func.toOption.any fun f =>
    (Stock.LiveCall.sourceData? f).isSome
  if !relevant || !LiveCallFile.modeB pf pre cleanup then
    return ← compileFileResultCallWhen true alloc pf pre cleanup
  let attempt ← compileFileWithLowering lowerForAllocationLiveCall VCode.rulesFired
    alloc pf pre cleanup
  finishFileVoidCallABI attempt (compileFileResultCallWhen true alloc pf pre cleanup)

theorem compileFileLiveCallWhen_disabled {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) :
    compileFileLiveCallWhen false alloc pf pre cleanup = compileFileResultCallWhen false alloc pf pre cleanup := by
  simp only [compileFileLiveCallWhen,Bool.not_false,ite_true]

theorem compileFileLiveCallWhen_retry {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool)
    (rejected : LiveCallFile.modeB pf pre cleanup = false) :
    compileFileLiveCallWhen true alloc pf pre cleanup = compileFileResultCallWhen true alloc pf pre cleanup := by
  simp only [compileFileLiveCallWhen,Bool.not_true,Bool.false_eq_true,ite_false,rejected,
    Bool.not_false,Bool.or_true,ite_true]

end Backend
