namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
variable {lower : ProductionLowering}

def attempt (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  let scope := if cleanup then inScopePar S.input0 else inScopeInPar S.input0
  if !scope then .error (if cleanup then outOfScopeMsg else outOfScopeInMsg)
  else
    let I := S.inputProductionWith lower cleanup
    if okRReturnPinCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) then
      leanLinkProductionWith lower S file0 cleanup
    else .error "the actual ABI-aware production pipeline checks failed"

end Link.ReturnPinCompilerWith
