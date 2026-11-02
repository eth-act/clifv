namespace Link.ReturnPinCompilerWitness
open Backend E2E E2E.LinkCheck E2E.SemanticBinary
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

def spec (cleanup : Bool) : LinkSpec := initial.placedProductionWith lower cleanup

def file0 (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (ProductionBoundaryWitness.plan (spec cleanup)) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

def file (cleanup : Bool) : ByteArray :=
  getOk (ReturnPinCompilerWith.attempt lower (spec cleanup) (file0 cleanup) cleanup)

def input (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  ReturnPinCompilerWith.input lower (spec cleanup) cleanup

#eval match ReturnPinCompilerWith.attempt lower (spec false) (file0 false) false with
  | .ok bytes => "mixed ELF: " ++ toString bytes.size ++ " bytes"
  | .error error => "mixed ELF failed: " ++ error

-- witness: native_decide (the complete unchanged mixed program in both cleanup modes)
theorem compiler_success (cleanup : Bool) :
    ReturnPinCompilerWith.attempt lower (spec cleanup) (file0 cleanup) cleanup = .ok (file cleanup) := by
  cases cleanup <;> native_decide

-- witness: native_decide (exact original source records in the two complete mixed programs)
theorem original_source (cleanup : Bool) :
    (input cleanup).funcs = PreparedReturnPinCallsWitness.input.funcs := by
  cases cleanup <;> native_decide

-- witness: native_decide (the old physical return contract rejects both complete mixed programs)
theorem old_rejected (cleanup : Bool) : SemanticStackBound.okB (input cleanup) = false := by
  cases cleanup <;> native_decide

private def stockChecks (cleanup : Bool) : Bool :=
  (prog (input cleanup)).funcs.all fun f => match Stock.lower f with
  | .error _ => false
  | .ok result => decide ((art (input cleanup) f).vc = result.code)

-- witness: native_decide (actual Stock artifacts for both unchanged mixed functions)
theorem actual_stock (cleanup : Bool) : stockChecks cleanup = true := by
  cases cleanup <;> native_decide

-- witness: native_decide (the complete unchanged mixed source contains no TLS instruction)
theorem no_tls (cleanup : Bool) : (prog (input cleanup)).funcs.all (fun f => !hasTls f) = true := by
  cases cleanup <;> native_decide

theorem contract (cleanup : Bool) :
    (SemanticStackBound.ofInput (input cleanup) closedBase (img (input cleanup))).OkSemanticReturnPins := by
  have checked := (ReturnPinCompilerWith.attempt_spec (compiler_success cleanup)).1
  have base : BaseOk (SemanticStackBound.ofInput (input cleanup) closedBase (img (input cleanup))) :=
    baseOk_closedR fun f member => by
      simpa only [Bool.not_eq_true'] using List.all_eq_true.mp (no_tls cleanup) f member
  exact ReturnPinBinary.okB_sound checked base (fun _ h => h)

#print axioms compiler_success
#print axioms original_source
#print axioms old_rejected
#print axioms actual_stock
#print axioms no_tls
#print axioms contract
end Link.ReturnPinCompilerWitness
