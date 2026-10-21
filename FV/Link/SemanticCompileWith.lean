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
end Link.SemanticCompilerWith
