import FV.Backend.Proof.StockFenceCompiledWitness
import FV.Opt.Legalize128Pre

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The original complete function contains no widened integer operation. -/
theorem mixed_no_i128 : Opt.Legalize128.mentions128 function = false := by native_decide -- witness: native_decide

/-- The existing legalizer leaves the original complete function unchanged. -/
theorem mixed_legalize_identity : Opt.Legalize128.legalize function = function := by
  simp [Opt.Legalize128.legalize,Opt.Legalize128.function128Cert,mixed_no_i128]

/-- The original-source compiler input produces both actual checked machine artifacts. -/
theorem mixed_original_complete_compilation (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc)
      (physical : AFunc) (assembly : FnAsm) (binary : FnBin),
      CompiledStockArithmeticStage (Opt.Legalize128.legalize function) cleanup 0
        result prepared allocated physical assembly binary := by
  rw [mixed_legalize_identity]
  exact mixed_complete_compilation cleanup

end Backend.Stock.Proof.FenceFixture
