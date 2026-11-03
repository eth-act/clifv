import FV.E2E.CompiledProduction
import FV.E2E.WorldReturnTraceLegacy
import FV.E2E.ValidatedReturnTraceW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

theorem worldReturnTraceProvider_production {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledProduction f k vc vcp rf af fa fb) :
    WorldReturnTraceProvider p f vc vcp rf af fa fb
      (fun us => us.map (·.2) = (List.range us.length).map Reg.x) := by
  cases hc with
  | legacy h => exact worldReturnTraceProvider_pipeline hsub h
  | stock h => exact worldReturnTraceProvider_validated hsub h
  | stockCleanup h => exact worldReturnTraceProvider_cleanup_validated hsub h

end E2E
