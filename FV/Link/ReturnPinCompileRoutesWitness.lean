import FV.Link.ReturnPinCompileRoutes
import FV.Link.ReturnPinRetryWitness
import FV.E2E.SemanticCompilerWitness

namespace Link.ReturnPinRoutedWitness
open Backend Backend.Stock.D0 E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The complete original mixed ELF selects the new ABI attempt in both cleanup modes. -/
theorem current_witness (cleanup : Bool) (previous : List ProductionLowering) :
    ReturnPinCompilerWith.compileWithRoutes ReturnPinRetryWitness.lower previous
      ReturnPinRetryWitness.initial (ReturnPinRetryWitness.file0 cleanup) cleanup =
      .ok ⟨ReturnPinRetryWitness.file cleanup,some 0⟩ := by
  exact ReturnPinCompilerWith.routes_current (ReturnPinRetryWitness.compiler_success cleanup)

private def mismatch (f : Clif.Function) : Except String VCode :=
  lowerFunction {f with blocks := f.blocks.map fun b =>
    {b with body := b.body.map fun stm =>
      {stm with inst := match stm.inst with
        | .binary .iadd ty x y => .binary .isub ty x y
        | .binary .band ty x y => .binary .bor ty x y
        | inst => inst}}}

private def previous : List ProductionLowering := [mismatch,mismatch,Stock.Arithmetic.lowerValidated]

private def retained (config : Configuration) (cleanup : Bool) : Bool :=
  let S := E2E.SemanticCompilerWitness.initial config
  let file0 := E2E.SemanticCompilerWitness.file0 config cleanup
  match SemanticCompilerWith.compileWithRoutes previous S file0 cleanup,
      ReturnPinCompilerWith.compileWithRoutes mismatch previous S file0 cleanup with
  | .ok old,.ok next => old.route == some 2 && next.route == some 3 && old.file.data == next.file.data
  | _,_ => false

/-- Rejection keeps a later shipped route, its complete bytes, and its exact shifted index. -/
theorem retained_route_witness :
    configurations.all (fun config => retained config false && retained config true) = true := by
  native_decide

end Link.ReturnPinRoutedWitness
