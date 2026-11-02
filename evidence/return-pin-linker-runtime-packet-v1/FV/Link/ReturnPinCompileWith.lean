import FV.Link.ReturnPinCompileDefs

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

theorem compile_accepted {current previous : ProductionLowering} {S : LinkSpec}
    {file0 file : ByteArray} {cleanup : Bool}
    (accepted : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok file) :
    compileWithFallback current previous S file0 cleanup = .ok ⟨file,true⟩ := by
  simp only [compileWithFallback,accepted]

theorem compile_retry {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {error : String}
    (rejected : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .error error) :
    compileWithFallback current previous S file0 cleanup = SemanticCompilerWith.compile previous S file0 cleanup := by
  simp only [compileWithFallback,rejected]

theorem compile_accepts_previous {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : SemanticCompilerWith.Output}
    (accepted : SemanticCompilerWith.compile previous S file0 cleanup = .ok out) :
    ∃ next,compileWithFallback current previous S file0 cleanup = .ok next := by
  unfold compileWithFallback
  split
  · exact ⟨_,rfl⟩
  · exact ⟨out,accepted⟩

theorem compile_spec {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : SemanticCompilerWith.Output}
    (compiled : compileWithFallback current previous S file0 cleanup = .ok out) :
    (out.stock = true ∧ attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok out.file) ∨
    SemanticCompilerWith.compile previous S file0 cleanup = .ok out := by
  unfold compileWithFallback at compiled
  split at compiled
  · cases compiled
    exact Or.inl ⟨rfl,by assumption⟩
  · exact Or.inr compiled

end Link.ReturnPinCompilerWith
