namespace Link.ReturnPinRetryWitness
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem choice_keeps_complete_stock (cleanup : Bool) :
    ReturnPinCompilerWith.compileWithChoice lower Stock.Production.lower initial (file0 cleanup) cleanup =
      .ok ⟨file cleanup,.current⟩ :=
  ReturnPinCompilerWith.choice_current (compiler_success cleanup)

def forcedRejection : ProductionLowering := fun _ => .error "the fixed witness rejects this lowering"

def choiceChecks (cleanup : Bool) : Bool :=
  (ReturnPinCompilerWith.compileWithChoice lower Stock.Production.lower rejected
    (rejectedFile0 cleanup) cleanup).toOption.any (fun out => decide (out.choice = .previous)) &&
  (ReturnPinCompilerWith.compileWithChoice forcedRejection forcedRejection rejected
    (rejectedFile0 cleanup) cleanup).toOption.any (fun out => decide (out.choice = .legacy))

attribute [local irreducible] lower initial rejected rejectedFile0 forcedRejection choiceChecks

-- witness: native_decide (actual previous and legacy compiler results in both cleanup modes)
theorem choice_checks : (choiceChecks false && choiceChecks true) = true := by native_decide

end Link.ReturnPinRetryWitness
