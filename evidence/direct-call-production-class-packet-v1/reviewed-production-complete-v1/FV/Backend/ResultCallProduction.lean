import FV.Backend.ReturnPinProduction
import FV.Backend.Lowering.StockResultCallRoutes

namespace Backend
set_option autoImplicit false

def lowerCheckedResultCall (f : Clif.Function) (verify : Bool) : Except String VCode := do
  let raw ← Stock.ResultCall.lowerValidated f
  if verify && !SemanticABI.checkResultCalls f raw then
    throw "lowering rejected by the proved result-call semantic validator"
  pure raw

def lowerForAllocationResultCall (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedResultCall f verify).map (Stock.Arithmetic.stage cleanup)

namespace ResultCallFile

def entry (f : Clif.Function) (verify cleanup : Bool) : Except String ReturnPinFile.Entry := do
  let raw ← lowerCheckedResultCall f verify
  let prepared ← prepare (Stock.Arithmetic.stage cleanup raw)
  pure ⟨f,raw,prepared,Thunk.mk (fun _ => ReturnPinCheck.pins f raw),rfl⟩

def entries (pf : Clif.ParsedFile) (pre : List (String × String))
    (cleanup : Bool) : Except String (List ReturnPinFile.Entry) :=
  pf.funcs.mapM fun parsed => do
    let f ← parsed.func.mapError (fun error => error.toString)
    let verify := ((unverifiedReason? f).isSome || (pre.lookup parsed.name).isSome ||
      (overBudget? f).isSome).not
    entry f verify cleanup

/-- Admission reads every actual artifact and its physical call metadata. -/
def modeB (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool) : Bool :=
  (entries pf pre cleanup).toOption.any fun actual =>
    actual.all (fun e => SemanticABI.checkResultCalls e.source e.raw) && ReturnPinFile.check actual

end ResultCallFile

/-- Keep a complete new file or retry the entire previous file with the original callback. -/
def compileFileResultCallWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileReturnPinWhen false alloc pf pre cleanup
  let relevant := pf.funcs.any fun parsed => parsed.func.toOption.any fun f =>
    (Stock.ResultCall.sourceData? f).isSome
  if !relevant || !ResultCallFile.modeB pf pre cleanup then
    return ← compileFileReturnPinWhen true alloc pf pre cleanup
  let attempt ← compileFileWithLowering lowerForAllocationResultCall VCode.rulesFired
    alloc pf pre cleanup
  finishFileVoidCallABI attempt (compileFileReturnPinWhen true alloc pf pre cleanup)

theorem compileFileResultCallWhen_disabled {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) :
    compileFileResultCallWhen false alloc pf pre cleanup = compileFileReturnPinWhen false alloc pf pre cleanup := by
  simp only [compileFileResultCallWhen,Bool.not_false,ite_true]

theorem compileFileResultCallWhen_retry {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool)
    (rejected : ResultCallFile.modeB pf pre cleanup = false) :
    compileFileResultCallWhen true alloc pf pre cleanup = compileFileReturnPinWhen true alloc pf pre cleanup := by
  simp only [compileFileResultCallWhen,Bool.not_true,Bool.false_eq_true,ite_false,rejected,
    Bool.not_false,Bool.or_true,ite_true]

end Backend
