import FV.Backend.Proof.StockAcquireCompiledWitness
import FV.Opt.Legalize128Pre

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The original complete function contains no widened integer operation. -/
theorem acquire_no_i128 : Opt.Legalize128.mentions128 function = false := by native_decide

/-- The existing legalizer leaves the original complete function unchanged. -/
theorem acquire_legalize_identity : Opt.Legalize128.legalize function = function := by
  simp [Opt.Legalize128.legalize,Opt.Legalize128.function128Cert,acquire_no_i128]

/-- The original-source compiler input produces both actual checked machine artifacts. -/
theorem acquire_original_complete_compilation (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc)
      (physical : AFunc) (assembly : FnAsm) (binary : FnBin),
      CompiledStockArithmeticStage (Opt.Legalize128.legalize function) cleanup 0
        result prepared allocated physical assembly binary := by
  rw [acquire_legalize_identity]
  exact acquire_complete_compilation cleanup

end Backend.Stock.Proof.Acquire810
