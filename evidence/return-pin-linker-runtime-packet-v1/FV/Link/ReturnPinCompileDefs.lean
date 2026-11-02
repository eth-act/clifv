import FV.Link.SemanticCompileDefs
import FV.E2E.PreparedReturnPinCalls

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

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Keep a complete checked attempt or run the complete previous compiler on its original input. -/
def compileWithFallback (current previous : ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) : Except String SemanticCompilerWith.Output :=
  match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,true⟩
  | .error _ => SemanticCompilerWith.compile previous S file0 cleanup

end Link.ReturnPinCompilerWith
