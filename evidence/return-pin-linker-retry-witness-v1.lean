namespace Link.ReturnPinCompilerWitness
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem compiler_keeps_complete_stock (cleanup : Bool) :
    ReturnPinCompilerWith.compileWithFallback lower Stock.Production.lower initial (file0 cleanup) cleanup =
      .ok ⟨file cleanup,true⟩ :=
  ReturnPinCompilerWith.compile_accepted (compiler_success cleanup)

/-- The additional caller has a nop outside the first call class. Keep the complete original callee. -/
def rejected : LinkSpec := {initial with funcs := PreparedReturnPinCallsWitness.rejectedInput.funcs}

def rejectedFile0 (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan
      (rejected.placedProductionWith Stock.Production.lower cleanup)) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

def retryChecks (cleanup : Bool) : Bool :=
  !(ReturnPinCompilerWith.attempt lower (rejected.placedProductionWith lower cleanup)
    (rejectedFile0 cleanup) cleanup).isOk &&
  (SemanticCompilerWith.compile Stock.Production.lower rejected (rejectedFile0 cleanup) cleanup).isOk

#eval (retryChecks false,retryChecks true)

-- witness: native_decide (the complete additional negative program in both cleanup modes)
theorem retry_checks : (retryChecks false && retryChecks true) = true := by native_decide

theorem compiler_retries_complete_previous (cleanup : Bool) :
    ReturnPinCompilerWith.compileWithFallback lower Stock.Production.lower rejected (rejectedFile0 cleanup) cleanup =
      SemanticCompilerWith.compile Stock.Production.lower rejected (rejectedFile0 cleanup) cleanup := by
  have both := Bool.and_eq_true_iff.mp retry_checks
  have checked : retryChecks cleanup = true := by cases cleanup <;> first | exact both.1 | exact both.2
  simp only [retryChecks,Bool.and_eq_true,Bool.not_eq_true'] at checked
  cases attempt : ReturnPinCompilerWith.attempt lower (rejected.placedProductionWith lower cleanup)
      (rejectedFile0 cleanup) cleanup with
  | ok bytes => simp only [attempt,Except.isOk] at checked; cases checked.1
  | error error => exact ReturnPinCompilerWith.compile_retry attempt

#print axioms compiler_keeps_complete_stock
#print axioms retry_checks
#print axioms compiler_retries_complete_previous
end Link.ReturnPinCompilerWitness
