import FV.E2E.SemanticCompilerWitness
import FV.E2E.SemanticMixedCompilerWitness

namespace E2E.SemanticFallbackWitness
open Backend Backend.Stock.D0 Link
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- A lowering error can recover inside the per-function pipeline. Instead,
produce allocatable code for a different computation so the complete program's
semantic checker rejects the first attempt. -/
private def mismatch (f : Clif.Function) : Except String VCode :=
  lowerFunction {f with blocks := f.blocks.map fun b =>
    {b with body := b.body.map fun stm =>
      {stm with inst := match stm.inst with
        | .binary .iadd ty x y => .binary .isub ty x y
        | inst => inst}}}

private def selected (r : Except String SemanticCompilerWith.FallbackOutput)
    (wanted : SemanticCompilerWith.CompileChoice) : Bool :=
  match r with | .error _ => false | .ok out => out.choice == wanted

private def legacyFile0 (config : Configuration) (cleanup : Bool) : ByteArray :=
  let spec := SemanticCompilerWith.legacySpec (SemanticCompilerWitness.initial config) cleanup
  match Link.Ld.assemble (SemanticCompilerWitness.plan spec) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

private def mixedPreviousFile0 (config : Configuration) (cleanup : Bool) : ByteArray :=
  let spec := (SemanticMixedCompilerWitness.initial config).placedProductionWith
    Stock.Arithmetic.lowerValidated cleanup
  match Link.Ld.assemble (SemanticMixedCompilerWitness.plan spec) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

private def mixedLegacyFile0 (config : Configuration) (cleanup : Bool) : ByteArray :=
  let spec := SemanticCompilerWith.legacySpec (SemanticMixedCompilerWitness.initial config) cleanup
  match Link.Ld.assemble (SemanticMixedCompilerWitness.plan spec) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

private def checks (config : Configuration) (cleanup : Bool) : Bool :=
  selected (SemanticCompilerWith.compileWithFallback Stock.Mixed.lowerValidated
    Stock.Arithmetic.lowerValidated (SemanticMixedCompilerWitness.initial config)
    (SemanticMixedCompilerWitness.file0 config cleanup) cleanup) .current &&
  selected (SemanticCompilerWith.compileWithFallback mismatch Stock.Arithmetic.lowerValidated
    (SemanticCompilerWitness.initial config) (SemanticCompilerWitness.file0 config cleanup) cleanup) .previous &&
  selected (SemanticCompilerWith.compileWithFallback mismatch mismatch
    (SemanticCompilerWitness.initial config) (legacyFile0 config cleanup) cleanup) .legacy &&
  selected (SemanticCompilerWith.compileWithFallback mismatch Stock.Arithmetic.lowerValidated
    (SemanticMixedCompilerWitness.initial config) (mixedPreviousFile0 config cleanup) cleanup) .previous &&
  selected (SemanticCompilerWith.compileWithFallback mismatch mismatch
    (SemanticMixedCompilerWitness.initial config) (mixedLegacyFile0 config cleanup) cleanup) .legacy

-- witness: native_decide (all three actual compiler choices, twelve configurations)
theorem checks_true : configurations.all (fun config => checks config false && checks config true) = true := by
  native_decide

end E2E.SemanticFallbackWitness
