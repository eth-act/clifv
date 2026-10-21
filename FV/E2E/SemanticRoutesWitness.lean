import FV.E2E.SemanticLogicalCompilerWitness
import FV.E2E.SemanticMixedCompilerWitness
import FV.E2E.SemanticCompilerWitness

namespace E2E.SemanticRoutesWitness
open Backend Backend.Stock.D0 Link
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def mismatch (f : Clif.Function) : Except String VCode :=
  lowerFunction {f with blocks := f.blocks.map fun b =>
    {b with body := b.body.map fun stm =>
      {stm with inst := match stm.inst with
        | .binary .iadd ty x y => .binary .isub ty x y
        | .binary .band ty x y => .binary .bor ty x y
        | inst => inst}}}

private def selected (r : Except String SemanticCompilerWith.RoutedOutput)
    (wanted : Option Nat) : Bool :=
  match r with | .error _ => false | .ok out => out.route == wanted

private def legacyFile0 (config : Configuration) (cleanup : Bool) : ByteArray :=
  let spec := SemanticCompilerWith.legacySpec (SemanticCompilerWitness.initial config) cleanup
  match Link.Ld.assemble (SemanticCompilerWitness.plan spec) with
  | .ok image => image.write
  | .error _ => ByteArray.empty

private def checks (config : Configuration) (cleanup : Bool) : Bool :=
  selected (SemanticCompilerWith.compileWithRoutes
    [Stock.Logical.lowerValidated,Stock.Mixed.lowerValidated,Stock.Arithmetic.lowerValidated]
    (SemanticLogicalCompilerWitness.initial config)
    (SemanticLogicalCompilerWitness.file0 config cleanup) cleanup) (some 0) &&
  selected (SemanticCompilerWith.compileWithRoutes
    [mismatch,Stock.Logical.lowerValidated,Stock.Mixed.lowerValidated,Stock.Arithmetic.lowerValidated]
    (SemanticLogicalCompilerWitness.initial config)
    (SemanticLogicalCompilerWitness.file0 config cleanup) cleanup) (some 1) &&
  selected (SemanticCompilerWith.compileWithRoutes [mismatch,Stock.Mixed.lowerValidated,Stock.Arithmetic.lowerValidated]
    (SemanticMixedCompilerWitness.initial config)
    (SemanticMixedCompilerWitness.file0 config cleanup) cleanup) (some 1) &&
  selected (SemanticCompilerWith.compileWithRoutes [mismatch,mismatch,Stock.Arithmetic.lowerValidated]
    (SemanticCompilerWitness.initial config)
    (SemanticCompilerWitness.file0 config cleanup) cleanup) (some 2) &&
  selected (SemanticCompilerWith.compileWithRoutes [mismatch,mismatch,mismatch]
    (SemanticCompilerWitness.initial config) (legacyFile0 config cleanup) cleanup) none

/-- Fixed complete compiler attempts exercise current, shifted current, retained
Mixed, retained Arithmetic and legacy routes across every ABI/cleanup setting. -/
theorem checks_true : configurations.all (fun config => checks config false && checks config true) = true := by
  native_decide

end E2E.SemanticRoutesWitness
