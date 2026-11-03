import FV.E2E.CompiledSemanticReturnPins
import FV.E2E.WorldReturnTraceProvider

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The actual checked pipeline constructs the ABI artifact and its full W return provider.
The provider remains internal. No source caller supplies an execution certificate. -/
theorem compiledCallStoreReturnTrace_of_checks
    {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.CallStore.check f vc = true) {cleanup : Bool}
    (prepared : Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true)
    (allocation : Backend.checkAlloc vcp rf = .ok ())
    (allocated : lowerRFunc vcp rf = .ok af)
    (emitted : emitFunc k af = .ok fa) (laidOut : fa.layout = .ok fb) :
    CompiledSemanticReturnPins f k vc vcp rf af fa fb .stockABI ∧
      WorldReturnTraceProvider p f vc vcp rf af fa fb (ReturnABI f) := by
  obtain ⟨result,lowered,equal,_,_,_,_,_⟩ := Stock.CallStore.check_sound checked
  have actual : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb :=
    ⟨lowered,by rwa [equal],by rwa [equal],allocation,allocated,emitted,laidOut⟩
  have accepted : Stock.CallStore.check f result.code = true := by rwa [equal]
  refine ⟨.callStore accepted equal actual,?_⟩
  have provider := worldReturnTraceProvider_callStore hsub accepted actual
  rwa [equal] at provider

end E2E
