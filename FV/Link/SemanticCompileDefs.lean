import FV.Link.ProductionImageWith
import FV.E2E.SemanticPipelineCheck
import FV.Link.DeadCleanupCompile
import FV.Link.Placed

/-! Executable transactional compilation. Correctness consumers remain in
`SemanticCompileWith`; runtime tools use these identical data definitions. -/
set_option autoImplicit false
namespace Link.SemanticCompilerWith
open Backend E2E E2E.LinkCheck
variable {lower : ProductionLowering}

def attempt (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  let scope := if cleanup then inScopePar S.input0 else inScopeInPar S.input0
  if !scope then .error (if cleanup then outOfScopeMsg else outOfScopeInMsg)
  else
    let I := S.inputProductionWith lower cleanup
    if okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) then
      leanLinkProductionWith lower S file0 cleanup
    else .error "the actual production pipeline checks failed"

/-- `attempt` with the Stock route's pipeline run once (`attempt_eq_fast`, `@[csimp]`): the
results the checks accept are the results the writer writes (`inputProductionWith`'s depth does
not change them). -/
def attemptFast (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) :
    Except String ByteArray :=
  let scope := if cleanup then inScopePar S.input0 else inScopeInPar S.input0
  if !scope then .error (if cleanup then outOfScopeMsg else outOfScopeInMsg)
  else
    let R := S.input0.resultsProductionWith lower cleanup
    if okRSemanticNI (productionStage cleanup) (S.input0.withDepth R) R then
      leanLinkWithResults S file0 (fun _ => R)
    else .error "the actual production pipeline checks failed"

@[csimp] theorem attempt_eq_fast : @attempt = @attemptFast := by
  funext lower S file0 cleanup
  have hl : leanLinkProductionWith lower S file0 cleanup =
      leanLinkWithResults S file0 (fun _ => S.input0.resultsProductionWith lower cleanup) :=
    leanLinkWithResults_congr S file0 (parResultsProductionWith_eq lower S.input0 cleanup)
  have hr : (S.input0.withDepth (S.input0.resultsProductionWith lower cleanup)).resultsProductionWith
      lower cleanup = S.input0.resultsProductionWith lower cleanup := rfl
  simp only [attempt, attemptFast, LinkSpec.inputProductionWith, hl, hr]

structure Output where
  file : ByteArray
  stock : Bool

def legacySpec (S : LinkSpec) (cleanup : Bool) : LinkSpec :=
  if cleanup then DeadCleanup.placedPar S else S.placedPar

def legacyCompile (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  if cleanup then DeadCleanup.compileExe S file0 else compileExe S file0

def compile (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String Output :=
  match attempt lower (S.placedProductionWith lower cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,true⟩
  | .error _ => (legacyCompile (legacySpec S cleanup) file0 cleanup).map fun file => ⟨file,false⟩

inductive CompileChoice where
  | current | previous | legacy
  deriving DecidableEq, Repr

structure FallbackOutput where
  file : ByteArray
  choice : CompileChoice

/-- Retry the previously shipped semantic compiler before the legacy compiler.
Every attempt receives the original specification, image and cleanup setting. -/
def compileWithFallback (current previous : ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) : Except String FallbackOutput :=
  match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,.current⟩
  | .error _ => (compile previous S file0 cleanup).map fun out =>
      ⟨out.file,if out.stock then .previous else .legacy⟩


/-- Actual output and its selected semantic route; none records legacy retry. -/
structure RoutedOutput where
  file : ByteArray
  route : Option Nat

/-- Extend the complete retry sequence without dropping a previously shipped
attempt. Every route receives the original specification/image/settings. -/
def compileWithRoutes (routes : List ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) : Except String RoutedOutput :=
  match routes with
  | [] => (legacyCompile (legacySpec S cleanup) file0 cleanup).map fun file => ⟨file,none⟩
  | current :: previous =>
    match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
    | .ok file => .ok ⟨file,some 0⟩
    | .error _ => (compileWithRoutes previous S file0 cleanup).map fun out =>
        ⟨out.file,out.route.map Nat.succ⟩

end Link.SemanticCompilerWith
