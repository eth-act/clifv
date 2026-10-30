import FV.E2E.ArithmeticPipeline
import FV.Clif.Print
import FV.E2E.StockArithmeticArtifactWitness
import FV.Backend.Proof.ArithmeticProduction

namespace E2E.ArithmeticPipelineWitness
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck
open StockArithmeticArtifactWitness (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

def fn : FnInput := {clif := function.print,ra := "null"}
def input : LinkInput := {
  funcs := [fn]
  addrs := [(function.name,0x200160)]
  syms := []
  raStar := 0x8000000
  D := 4096
  fallback := true }

private def checks (cleanup : Bool) : Bool :=
  match input.pipeArithmetic cleanup fn with
  | .error _ => false
  | .ok a =>
    (staticChksSemantic cleanup input fn.func (.ok a)).all (·.2) &&
    !lowerCheck fn.func a.vc

/-- Fixed parser/compiler/linker-input data. Both settings retain actual Stock
code through the semantic checker instead of silently taking legacy fallback. -/
theorem checks_true : (checks false && checks true) = true := by native_decide

/-- A real parsed input traverses the actual transactional link pipeline and
constructs a semantic artifact outside the old lowering-validator domain. -/
theorem pipeline_exists (cleanup : Bool) :
    ∃ a, input.pipeArithmetic cleanup fn = .ok a ∧
      CompiledSemantic fn.func a.k a.vc a.vcp a.rf a.af a.fa a.fb ∧
      lowerCheck fn.func a.vc = false ∧
      (staticChksSemantic cleanup input fn.func (.ok a)).all (·.2) = true := by
  have h : checks cleanup = true := by
    have both := checks_true
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  cases run : input.pipeArithmetic cleanup fn with
  | error message => simp [checks,run] at h
  | ok a =>
    simp only [checks,run,Bool.and_eq_true,Bool.not_eq_true'] at h
    exact ⟨a,rfl,LinkInput.pipeArithmetic_compiled run h.1,h.2,h.1⟩

/-- Failure retries use the same real source input and the previously shipped
route; this witness exercises the error branch of the runtime adapter. -/
example : lowerCheckedSemanticWith (fun _ => .error "candidate failure") fn.func true =
    lowerCheckedProductionWith Stock.ScalarAdd.lower fn.func true :=
  lowerCheckedSemanticWith_retry rfl

end E2E.ArithmeticPipelineWitness
