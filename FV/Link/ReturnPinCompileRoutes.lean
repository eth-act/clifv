import FV.Link.ReturnPinCompileDefs
import FV.Link.SemanticCompileWith

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Add the ABI attempt before the complete previously shipped route sequence. -/
def shiftPrevious (out : SemanticCompilerWith.RoutedOutput) : SemanticCompilerWith.RoutedOutput :=
  ⟨out.file,out.route.map Nat.succ⟩

def unshiftPrevious (out : SemanticCompilerWith.RoutedOutput) : SemanticCompilerWith.RoutedOutput :=
  ⟨out.file,out.route.map Nat.pred⟩

def compileWithRoutes (current : ProductionLowering) (previous : List ProductionLowering)
    (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String SemanticCompilerWith.RoutedOutput :=
  match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,some 0⟩
  | .error _ => (SemanticCompilerWith.compileWithRoutes previous S file0 cleanup).map shiftPrevious

theorem unshift_shift (out : SemanticCompilerWith.RoutedOutput) :
    unshiftPrevious (shiftPrevious out) = out := by
  cases out with
  | mk file route => cases route <;> rfl

theorem shift_file (out : SemanticCompilerWith.RoutedOutput) : (shiftPrevious out).file = out.file := rfl

theorem routes_current {current : ProductionLowering} {previous : List ProductionLowering}
    {S : LinkSpec} {file0 file : ByteArray} {cleanup : Bool}
    (accepted : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok file) :
    compileWithRoutes current previous S file0 cleanup = .ok ⟨file,some 0⟩ := by
  simp only [compileWithRoutes,accepted]

theorem routes_retry {current : ProductionLowering} {previous : List ProductionLowering}
    {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {error : String}
    (rejected : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .error error) :
    compileWithRoutes current previous S file0 cleanup =
      (SemanticCompilerWith.compileWithRoutes previous S file0 cleanup).map shiftPrevious := by
  simp only [compileWithRoutes,rejected]

/-- Every previously successful complete route sequence remains accepted. -/
theorem routes_accepts_previous {current : ProductionLowering} {previous : List ProductionLowering}
    {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {out : SemanticCompilerWith.RoutedOutput}
    (accepted : SemanticCompilerWith.compileWithRoutes previous S file0 cleanup = .ok out) :
    ∃ next,compileWithRoutes current previous S file0 cleanup = .ok next := by
  unfold compileWithRoutes
  split
  · exact ⟨_,rfl⟩
  · rw [accepted]
    exact ⟨_,rfl⟩

/-- Rejection preserves every previous byte and restores its exact route metadata. -/
theorem routes_retry_erases {current : ProductionLowering} {previous : List ProductionLowering}
    {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {error : String}
    (rejected : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .error error) :
    (compileWithRoutes current previous S file0 cleanup).map unshiftPrevious =
      SemanticCompilerWith.compileWithRoutes previous S file0 cleanup := by
  rw [routes_retry rejected]
  cases prior : SemanticCompilerWith.compileWithRoutes previous S file0 cleanup with
  | error message => rfl
  | ok out => simpa only [Except.map,unshift_shift]

theorem routes_previous_error {current : ProductionLowering} {previous : List ProductionLowering}
    {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {firstError previousError : String}
    (rejected : attempt current (S.placedProductionWith current cleanup) file0 cleanup = .error firstError)
    (failed : SemanticCompilerWith.compileWithRoutes previous S file0 cleanup = .error previousError) :
    compileWithRoutes current previous S file0 cleanup = .error previousError := by
  rw [routes_retry rejected,failed]
  rfl

/-- Every retained index identifies the exact complete compiler attempt that wrote the file. -/
theorem routes_spec {current : ProductionLowering} {previous : List ProductionLowering}
    {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {out : SemanticCompilerWith.RoutedOutput}
    (compiled : compileWithRoutes current previous S file0 cleanup = .ok out) :
    (out.route = some 0 ∧ attempt current (S.placedProductionWith current cleanup) file0 cleanup = .ok out.file) ∨
    (out.route = none ∧ SemanticCompilerWith.legacyCompile (SemanticCompilerWith.legacySpec S cleanup)
      file0 cleanup = .ok out.file) ∨
    ∃ index lower,out.route = some (index+1) ∧ previous[index]? = some lower ∧
      SemanticCompilerWith.attempt lower (S.placedProductionWith lower cleanup) file0 cleanup = .ok out.file := by
  unfold compileWithRoutes at compiled
  split at compiled
  · cases compiled
    exact Or.inl ⟨rfl,by assumption⟩
  · cases prior : SemanticCompilerWith.compileWithRoutes previous S file0 cleanup with
    | error error => simp only [prior,Except.map] at compiled; cases compiled
    | ok old =>
      simp only [prior,Except.map] at compiled
      cases compiled
      rcases SemanticCompilerWith.compileWithRoutes_spec prior with legacy | ⟨index,lower,route,found,run⟩
      · exact Or.inr (Or.inl ⟨by simp [shiftPrevious,legacy.1],legacy.2⟩)
      · exact Or.inr (Or.inr ⟨index,lower,by simp [shiftPrevious,route],found,run⟩)

end Link.ReturnPinCompilerWith
