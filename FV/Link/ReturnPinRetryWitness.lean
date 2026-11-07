import FV.Link.ReturnPinCompileWith
import FV.E2E.PreparedReturnPinCallsWitness
import FV.E2E.ProductionBoundaryWitness

namespace Link.ReturnPinRetryWitness
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def lower : ProductionLowering := Stock.VoidCall.NI.lowerValidated

def initial : LinkSpec := {
  funcs := PreparedReturnPinCallsWitness.input.funcs
  names := []
  sizes := []
  outside := []
  symNames := PreparedReturnPinCallsWitness.input.funcs.map (fun entry => entry.func.name)
  R := 0x200160 }

def rejected : LinkSpec := {initial with funcs := PreparedReturnPinCallsWitness.rejectedInput.funcs}

def rejectedFile0 (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan
      (rejected.placedProductionWith Stock.Production.lower cleanup)) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

/-- Since #587 (#931 fixed) the return-pin attempt accepts the nop-caller fixture `rejected`
(before, it rejected it and the compiler retried with the previous pipeline). -/
def retryChecks (cleanup : Bool) : Bool :=
  (ReturnPinCompilerWith.attempt lower (rejected.placedProductionWith lower cleanup)
    (rejectedFile0 cleanup) cleanup).isOk &&
  (SemanticCompilerWith.compile Stock.Production.lower rejected (rejectedFile0 cleanup) cleanup).isOk


attribute [local irreducible] lower initial rejected rejectedFile0 retryChecks

-- witness: native_decide (the complete additional program in both cleanup modes)
theorem retry_checks : (retryChecks false && retryChecks true) = true := by native_decide

/-- The compiler keeps the return-pin attempt's output for the fixture `rejected`. Before #587
this stated the retry with the previous pipeline (`SemanticCompilerWith.compile`); #931 is
fixed, so the attempt now succeeds and no retry happens. -/
theorem compiler_retries_complete_previous (cleanup : Bool) :
    ReturnPinCompilerWith.compileWithFallback lower Stock.Production.lower rejected (rejectedFile0 cleanup) cleanup =
      .ok ⟨getOk (ReturnPinCompilerWith.attempt lower (rejected.placedProductionWith lower cleanup)
        (rejectedFile0 cleanup) cleanup),true⟩ := by
  have both := Bool.and_eq_true_iff.mp retry_checks
  have checked : retryChecks cleanup = true := by cases cleanup <;> first | exact both.1 | exact both.2
  simp only [retryChecks,Bool.and_eq_true] at checked
  cases attempt : ReturnPinCompilerWith.attempt lower (rejected.placedProductionWith lower cleanup)
      (rejectedFile0 cleanup) cleanup with
  | ok bytes => exact ReturnPinCompilerWith.compile_accepted attempt
  | error error => simp only [attempt,Except.isOk] at checked; cases checked.1

end Link.ReturnPinRetryWitness

namespace Link.ReturnPinRetryWitness
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def spec (cleanup : Bool) : LinkSpec := initial.placedProductionWith lower cleanup

def file0 (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan (spec cleanup)) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

def file (cleanup : Bool) : ByteArray :=
  getOk (ReturnPinCompilerWith.attempt lower (spec cleanup) (file0 cleanup) cleanup)

attribute [local irreducible] lower initial file0 file

-- witness: native_decide (actual complete original mixed program in both cleanup modes)
theorem compiler_success (cleanup : Bool) :
    ReturnPinCompilerWith.attempt lower (spec cleanup) (file0 cleanup) cleanup = .ok (file cleanup) := by
  cases cleanup <;> native_decide

theorem compiler_keeps_complete_stock (cleanup : Bool) :
    ReturnPinCompilerWith.compileWithFallback lower Stock.Production.lower initial (file0 cleanup) cleanup =
      .ok ⟨file cleanup,true⟩ :=
  ReturnPinCompilerWith.compile_accepted (compiler_success cleanup)

end Link.ReturnPinRetryWitness

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

/-- A fixed incorrect compiler omits stores while retaining a valid allocation pipeline. -/
def storeDroppingLower : ProductionLowering := fun f =>
  (lowerFunction f).map fun vc => {vc with blocks := vc.blocks.map fun block =>
    {block with insts := block.insts.filter fun | .store _ _ _ _ => false | _ => true}}

/-- Since #587 (#931 fixed) the correct compiler's choice for `rejected` is `.current` (before:
`.previous`, after the return-pin attempt rejected it). -/
def choiceChecks (cleanup : Bool) : Bool :=
  (ReturnPinCompilerWith.compileWithChoice lower Stock.Production.lower rejected
    (rejectedFile0 cleanup) cleanup).toOption.any (fun out => decide (out.choice = .current)) &&
  (ReturnPinCompilerWith.compileWithChoice storeDroppingLower storeDroppingLower rejected
    (rejectedFile0 cleanup) cleanup).toOption.any (fun out => decide (out.choice = .legacy))

attribute [local irreducible] lower initial rejected rejectedFile0 storeDroppingLower choiceChecks

-- witness: native_decide (actual previous and legacy compiler results in both cleanup modes)
theorem choice_checks : (choiceChecks false && choiceChecks true) = true := by native_decide

end Link.ReturnPinRetryWitness
