import FV.Link.SemanticCompileDefs
import FV.E2E.ReturnPinAdmission

namespace Link.ReturnPinAttemptKernel
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

def attemptWith (checked : (Clif.Function → VCode → VCode) → LinkInput → Res → Bool) (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  let scope := if cleanup then inScopePar S.input0 else inScopeInPar S.input0
  if !scope then .error (if cleanup then outOfScopeMsg else outOfScopeInMsg)
  else
    let I := S.inputProductionWith lower cleanup
    if checked (productionStage cleanup) I (I.resultsProductionWith lower cleanup) then
      leanLinkProductionWith lower S file0 cleanup
    else .error "the actual ABI-aware production pipeline checks failed"


end Link.ReturnPinAttemptKernel
