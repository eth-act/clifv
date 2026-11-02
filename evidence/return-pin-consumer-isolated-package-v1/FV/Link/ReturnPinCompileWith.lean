import FV.Link.ReturnPinCompileDefs
import FV.Link.SemanticCompileWith

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

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

theorem choice_current {current previous : ProductionLowering} {S : LinkSpec}
    {file0 file : ByteArray} {cleanup : Bool}
    (accepted : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok file) :
    compileWithChoice current previous S file0 cleanup = .ok ⟨file,.current⟩ := by
  simp only [compileWithChoice,accepted]

theorem choice_retry {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {error : String}
    (rejected : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .error error) :
    compileWithChoice current previous S file0 cleanup =
      (SemanticCompilerWith.compile previous S file0 cleanup).map (fun out =>
        ⟨out.file,if out.stock then .previous else .legacy⟩) := by
  simp only [compileWithChoice,rejected]

theorem choice_accepts_previous {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : SemanticCompilerWith.Output}
    (accepted : SemanticCompilerWith.compile previous S file0 cleanup = .ok out) :
    ∃ next,compileWithChoice current previous S file0 cleanup = .ok next := by
  unfold compileWithChoice
  split
  · exact ⟨_,rfl⟩
  · rw [accepted]
    exact ⟨_,rfl⟩

/-- Every retained tag names the actual compiler that produced the complete linked bytes. -/
theorem choice_spec {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : SemanticCompilerWith.FallbackOutput}
    (compiled : compileWithChoice current previous S file0 cleanup = .ok out) :
    (out.choice = .current ∧ attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok out.file) ∨
    (out.choice = .previous ∧ SemanticCompilerWith.attempt previous
      (S.placedProductionWith previous cleanup) file0 cleanup = .ok out.file) ∨
    (out.choice = .legacy ∧ SemanticCompilerWith.legacyCompile
      (SemanticCompilerWith.legacySpec S cleanup) file0 cleanup = .ok out.file) := by
  unfold compileWithChoice at compiled
  split at compiled
  · cases compiled
    exact Or.inl ⟨rfl,by assumption⟩
  · cases prior : SemanticCompilerWith.compile previous S file0 cleanup with
    | error error =>
      simp only [prior,Except.map] at compiled
      cases compiled
    | ok old =>
      simp only [prior,Except.map] at compiled
      cases compiled
      rcases SemanticCompilerWith.compile_spec prior with checked | legacy
      · exact Or.inr (Or.inl ⟨by simp [checked.1],checked.2⟩)
      · exact Or.inr (Or.inr ⟨by simp [legacy.1],legacy.2⟩)

/-- Erasing only the tag preserves every byte and the complete compatibility result. -/
theorem choice_erases (current previous : ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) :
    (compileWithChoice current previous S file0 cleanup).map eraseChoice =
      compileWithFallback current previous S file0 cleanup := by
  unfold compileWithChoice compileWithFallback
  split
  · rfl
  · cases prior : SemanticCompilerWith.compile previous S file0 cleanup with
    | error error => rfl
    | ok old =>
      cases old with
      | mk file stock => cases stock <;> rfl

theorem choice_preserves_previous_error {current previous : ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {currentError previousError : String}
    (rejected : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .error currentError)
    (failed : SemanticCompilerWith.compile previous S file0 cleanup = .error previousError) :
    compileWithChoice current previous S file0 cleanup = .error previousError := by
  rw [choice_retry rejected,failed]
  rfl

end Link.ReturnPinCompilerWith
