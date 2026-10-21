import FV.Link.ProductionImageWith
import FV.E2E.SemanticPipelineCheck
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

end Link.SemanticCompilerWith
