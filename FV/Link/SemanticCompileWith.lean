import FV.Link.ProductionImageWith
import FV.E2E.SemanticStackBound
import FV.Link.Placed

/-! Transactional executable compilation. The legacy layout and compiler are
retained for a failed complete Stock attempt. Output records routing data only. -/
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

theorem accepts_legacy {S : LinkSpec} {file0 file : ByteArray} {cleanup : Bool}
    (h : legacyCompile (legacySpec S cleanup) file0 cleanup = .ok file) :
    ∃ out, compile lower S file0 cleanup = .ok out := by
  unfold compile
  split
  · exact ⟨_,rfl⟩
  · exact ⟨⟨file,false⟩,by rw [h]; rfl⟩

theorem compile_spec {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {out : Output}
    (h : compile lower S file0 cleanup = .ok out) :
    (out.stock = true ∧ attempt lower (S.placedProductionWith lower cleanup) file0 cleanup = .ok out.file) ∨
    (out.stock = false ∧ legacyCompile (legacySpec S cleanup) file0 cleanup = .ok out.file) := by
  unfold compile at h
  split at h
  · rename_i file hp
    cases h
    exact .inl ⟨rfl,hp⟩
  · rename_i e hp
    cases hl : legacyCompile (legacySpec S cleanup) file0 cleanup <;> simp only [hl,Except.map] at h
    · cases h
    · cases h
      exact .inr ⟨rfl,rfl⟩

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

theorem accepts_previous {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : Output}
    (h : compile previous S file0 cleanup = .ok out) :
    ∃ result, compileWithFallback current previous S file0 cleanup = .ok result := by
  unfold compileWithFallback
  split
  · exact ⟨_,rfl⟩
  · exact ⟨_,by rw [h]; rfl⟩

/-- Each selected result is an existing proved executable attempt or the
retained legacy compiler. Routing data introduces no new source premise. -/
theorem compileWithFallback_spec {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : FallbackOutput}
    (h : compileWithFallback current previous S file0 cleanup = .ok out) :
    (out.choice = .current ∧
      attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok out.file) ∨
    (out.choice = .previous ∧
      attempt previous (S.placedProductionWith previous cleanup) file0 cleanup = .ok out.file) ∨
    (out.choice = .legacy ∧ legacyCompile (legacySpec S cleanup) file0 cleanup = .ok out.file) := by
  unfold compileWithFallback at h
  split at h
  · rename_i file succeeded
    cases h
    exact .inl ⟨rfl,succeeded⟩
  · cases older : compile previous S file0 cleanup with
    | error message => simp only [older,Except.map] at h; cases h
    | ok result =>
      simp only [older,Except.map] at h
      cases h
      rcases compile_spec older with ⟨stock,run⟩ | ⟨legacy,run⟩
      · exact .inr (.inl ⟨by simp [stock],run⟩)
      · exact .inr (.inr ⟨by simp [legacy],run⟩)
end Link.SemanticCompilerWith
