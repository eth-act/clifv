import FV.Link.SemanticCompileDefs
import FV.E2E.SemanticStackBound

/-! Correctness of the actual transactional executable compiler. Public
compiler definitions retain their names and are imported from the runtime owner. -/
set_option autoImplicit false
namespace Link.SemanticCompilerWith
open Backend E2E E2E.LinkCheck
variable {lower : ProductionLowering}

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
