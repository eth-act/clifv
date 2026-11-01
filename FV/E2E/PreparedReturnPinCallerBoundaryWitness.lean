import FV.E2E.PreparedReturnPinSretWitness

namespace E2E.PreparedReturnPinCallerBoundaryWitness
open Backend E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private def callerText : String := "function %sret_caller(i64, i64) system_v {\n    fn0 = colocated %_RNxC7fv_demo11HawPMC3YC2b(i64 sret, i64) system_v\nblock0(v0: i64, v1: i64):\n    call fn0(v0, v1)\n    return\n}\n"
def input : LinkInput := {PreparedReturnPinSretWitness.input with
  funcs := PreparedReturnPinSretWitness.input.funcs ++ [{clif := callerText,ra := "null"}],
  addrs := PreparedReturnPinSretWitness.input.addrs ++ [("sret_caller",12288)]}
def outputs (cleanup : Bool) : Res := input.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup

/-- Every old check passes, but the actual legacy caller expects the implicit result in x0. -/
private def boundary (cleanup : Bool) : Bool :=
  okRSemanticFor Stock.MemorySretCopy.check (productionStage cleanup) input (outputs cleanup) &&
  !okRReturnPins (productionStage cleanup) input (outputs cleanup) &&
  returnPinChecks input (outputs cleanup) input.funcs[0]!.func &&
  !returnPinChecks input (outputs cleanup) input.funcs[1]!.func &&
  Proof.Driver.lowerCheck input.funcs[1]!.func (artOf (outputs cleanup) input.funcs[1]!.func).vc

attribute [local irreducible] boundary
-- witness: native_decide (the two fixed complete mixed programs only)
private theorem boundary_true : (boundary false && boundary true) = true := by native_decide

/-- The actual mixed program passes all old checks and fails only physical return compatibility.
A proved caller adapter must precede its cutover. -/
theorem legacy_caller_rejected_witness (cleanup : Bool) :
    okRSemanticFor Stock.MemorySretCopy.check (productionStage cleanup) input (outputs cleanup) = true ∧
      okRReturnPins (productionStage cleanup) input (outputs cleanup) = false ∧
      returnPinChecks input (outputs cleanup) input.funcs[0]!.func = true ∧
      returnPinChecks input (outputs cleanup) input.funcs[1]!.func = false ∧
      Proof.Driver.lowerCheck input.funcs[1]!.func (artOf (outputs cleanup) input.funcs[1]!.func).vc = true := by
  have both := Bool.and_eq_true_iff.mp boundary_true
  have checked : boundary cleanup = true := by
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simpa only [boundary,Bool.and_eq_true,Bool.not_eq_true',and_assoc] using checked

end E2E.PreparedReturnPinCallerBoundaryWitness
