import FV.E2E.CompiledEitherW
import FV.E2E.WorldReturnTraceCore

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The legacy artifact keeps its exact return convention and full paired field. -/
theorem worldReturnTraceProvider_pipeline {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb) :
    WorldReturnTraceProvider p f vc vcp rf af fa fb
      (fun us => us.map (·.2) = (List.range us.length).map Reg.x) where
  run := backend_correct_world_niX_pipelineW hsub hc


end E2E
