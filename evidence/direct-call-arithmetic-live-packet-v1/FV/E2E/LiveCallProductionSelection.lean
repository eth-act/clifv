import FV.Backend.LiveCallProduction
import FV.E2E.LiveCallProductionExec
import FV.E2E.StockLiveCallWitness

namespace E2E.LiveCallProductionSelection
open Backend LiveCallProductionExec
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def source : Clif.ParsedFile := Clif.parseFile (callerText ++ calleeText)
private def selectedB (cleanup : Bool) : Bool :=
  LiveCallFile.modeB source [] cleanup && source.funcs.any (fun parsed =>
    parsed.func.toOption.any (fun f => (Stock.LiveCall.sourceData? f).isSome))
attribute [local irreducible] selectedB
-- witness: native_decide (the original complete input and actual default admission only)
theorem selected (cleanup : Bool) : selectedB cleanup = true := by
  cases cleanup <;> native_decide

/-- The real file entrypoint selects the new callback and retains its complete previous retry. -/
theorem actual_entrypoint {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (cleanup : Bool) :
    compileFileLiveCallWhen true alloc source [] cleanup = (do
      let attempt ← compileFileWithLowering lowerForAllocationLiveCall VCode.rulesFired
        alloc source [] cleanup
      finishFileVoidCallABI attempt (compileFileResultCallWhen true alloc source [] cleanup)) := by
  have facts := selected cleanup
  simp only [selectedB,Bool.and_eq_true] at facts
  simp only [compileFileLiveCallWhen,Bool.not_true,Bool.false_eq_true,ite_false,
    facts.1,facts.2,Bool.not_true,Bool.or_self]

/-- The actual predecessor accepts the caller, but the live provider selects its distinct Stock code. -/
-- witness: native_decide (fixed source and actual retained pipeline data only)
theorem actual_provider (cleanup : Bool) :
    ∃ (result : Stock.Result) (previous : VCode),Stock.lower LiveCallFixture.caller = .ok result ∧
      Stock.ResultCall.lowerValidated LiveCallFixture.caller = .ok previous ∧
      Stock.LiveCall.lowerWithPrevious Stock.ResultCall.lowerValidated LiveCallFixture.caller = .ok result.code ∧
      result.code ≠ previous ∧ Stock.LiveCall.Domain LiveCallFixture.caller result.code :=
  LiveCallWitness.actual_provider cleanup

def floatText : String := "function %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n return v0\n}\n"
def mixedSource : Clif.ParsedFile := Clif.parseFile (callerText ++ calleeText ++ floatText)
-- witness: native_decide (the unchanged distinct float input rejects new whole-file admission)
theorem mixed_rejected (cleanup : Bool) : LiveCallFile.modeB mixedSource [] cleanup = false := by
  cases cleanup <;> native_decide

/-- The mixed typed file retains the complete previous file action and original allocation callback. -/
theorem mixed_complete_retry {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (cleanup : Bool) :
    compileFileLiveCallWhen true alloc mixedSource [] cleanup =
      compileFileResultCallWhen true alloc mixedSource [] cleanup :=
  compileFileLiveCallWhen_retry alloc mixedSource [] cleanup (mixed_rejected cleanup)

end E2E.LiveCallProductionSelection
