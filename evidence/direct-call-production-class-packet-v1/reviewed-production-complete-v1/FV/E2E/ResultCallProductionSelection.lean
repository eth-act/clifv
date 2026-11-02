import FV.Backend.ResultCallProduction
import FV.E2E.ResultCallProductionExec
import FV.E2E.StockResultCallWitness

namespace E2E.ResultCallProductionSelection
open Backend ResultCallProductionExec
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def source : Clif.ParsedFile := Clif.parseFile (callerText ++ calleeText)
private def selectedB (cleanup : Bool) : Bool :=
  ResultCallFile.modeB source [] cleanup && source.funcs.any (fun parsed =>
    parsed.func.toOption.any (fun f => (Stock.ResultCall.sourceData? f).isSome))
attribute [local irreducible] selectedB
-- witness: native_decide (the original complete input and actual default admission only)
theorem selected (cleanup : Bool) : selectedB cleanup = true := by
  cases cleanup <;> native_decide

/-- The real file entrypoint selects the new callback and retains its complete previous retry. -/
theorem actual_entrypoint {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (cleanup : Bool) :
    compileFileResultCallWhen true alloc source [] cleanup = (do
      let attempt ← compileFileWithLowering lowerForAllocationResultCall VCode.rulesFired
        alloc source [] cleanup
      finishFileVoidCallABI attempt (compileFileReturnPinWhen true alloc source [] cleanup)) := by
  have facts := selected cleanup
  simp only [selectedB,Bool.and_eq_true] at facts
  simp only [compileFileResultCallWhen,Bool.not_true,Bool.false_eq_true,ite_false,
    facts.1,facts.2,Bool.not_true,Bool.or_self]

/-- Actual default selection retains source31, mapped193, fresh194, and physical x0. -/
theorem actual_provider (cleanup : Bool) :
    ∃ (result : Stock.Result) (previous : VCode) (prepared : VCode) (allocated : RFunc)
      (frame : AFunc) (assembly : FnAsm) (binary : FnBin),
      Stock.VoidCall.NI.lowerValidated Stock.Proof.DirectCallResultFixture.caller = .ok previous ∧
      Stock.ResultCall.lowerValidated Stock.Proof.DirectCallResultFixture.caller = .ok result.code ∧
      result.code ≠ previous ∧
      E2E.CompiledStockArithmeticStage Stock.Proof.DirectCallResultFixture.caller cleanup 0
        result prepared allocated frame assembly binary ∧
      Nonempty (Stock.Proof.DirectCallResult.Binding result.ctx result.final 31) :=
  ResultCallWitness.actual_predecessor_selection cleanup
def floatText : String := "function %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n return v0\n}\n"
def mixedSource : Clif.ParsedFile := Clif.parseFile (callerText ++ calleeText ++ floatText)
-- witness: native_decide (the unchanged distinct float input rejects new whole-file admission)
theorem mixed_rejected (cleanup : Bool) : ResultCallFile.modeB mixedSource [] cleanup = false := by
  cases cleanup <;> native_decide

/-- The mixed typed file retains the complete previous file action and original allocation callback. -/
theorem mixed_complete_retry {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (cleanup : Bool) :
    compileFileResultCallWhen true alloc mixedSource [] cleanup =
      compileFileReturnPinWhen true alloc mixedSource [] cleanup :=
  compileFileResultCallWhen_retry alloc mixedSource [] cleanup (mixed_rejected cleanup)

end E2E.ResultCallProductionSelection
