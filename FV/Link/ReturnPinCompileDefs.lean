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

/-- `attempt` with the Stock route's pipeline run once (`attempt_eq_fast`, `@[csimp]`; as
`SemanticCompilerWith.attemptFast`). -/
def attemptFast (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) :
    Except String ByteArray :=
  let scope := if cleanup then inScopePar S.input0 else inScopeInPar S.input0
  if !scope then .error (if cleanup then outOfScopeMsg else outOfScopeInMsg)
  else
    let R := S.input0.resultsProductionWith lower cleanup
    if okRReturnPinCalls (productionStage cleanup) (S.input0.withDepth R) R then
      leanLinkWithResults S file0 (fun _ => R)
    else .error "the actual ABI-aware production pipeline checks failed"

@[csimp] theorem attempt_eq_fast : @attempt = @attemptFast := by
  funext lower S file0 cleanup
  have hl : leanLinkProductionWith lower S file0 cleanup =
      leanLinkWithResults S file0 (fun _ => S.input0.resultsProductionWith lower cleanup) :=
    leanLinkWithResults_congr S file0 (parResultsProductionWith_eq lower S.input0 cleanup)
  have hr : (S.input0.withDepth (S.input0.resultsProductionWith lower cleanup)).resultsProductionWith
      lower cleanup = S.input0.resultsProductionWith lower cleanup := rfl
  simp only [attempt, attemptFast, LinkSpec.inputProductionWith, hl, hr]

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
namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false

/-- Keep the existing compiler tag with the complete selected output. -/
def compileWithChoice (current previous : ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) : Except String SemanticCompilerWith.FallbackOutput :=
  match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,.current⟩
  | .error _ => (SemanticCompilerWith.compile previous S file0 cleanup).map fun out =>
      ⟨out.file,if out.stock then .previous else .legacy⟩

def eraseChoice (out : SemanticCompilerWith.FallbackOutput) : SemanticCompilerWith.Output :=
  ⟨out.file,match out.choice with | .legacy => false | _ => true⟩

end Link.ReturnPinCompilerWith
