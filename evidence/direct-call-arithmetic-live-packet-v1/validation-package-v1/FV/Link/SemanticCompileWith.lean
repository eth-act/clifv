import FV.Link.SemanticCompileDefs

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

/-- A successful older complete route is preserved when a new route is added. -/
theorem compileWithRoutes_accepts_tail {current : ProductionLowering}
    {previous : List ProductionLowering} {S : LinkSpec} {file0 : ByteArray}
    {cleanup : Bool} {out : RoutedOutput}
    (h : compileWithRoutes previous S file0 cleanup = .ok out) :
    ∃ result, compileWithRoutes (current :: previous) S file0 cleanup = .ok result := by
  simp only [compileWithRoutes]
  split
  · exact ⟨_,rfl⟩
  · exact ⟨_,by rw [h]; rfl⟩

/-- The original legacy acceptance is preserved for any finite route list. -/
theorem compileWithRoutes_accepts_legacy {routes : List ProductionLowering}
    {S : LinkSpec} {file0 file : ByteArray} {cleanup : Bool}
    (h : legacyCompile (legacySpec S cleanup) file0 cleanup = .ok file) :
    ∃ out, compileWithRoutes routes S file0 cleanup = .ok out := by
  induction routes with
  | nil => exact ⟨⟨file,none⟩,by simp [compileWithRoutes,h,Except.map]⟩
  | cons current previous ih =>
    obtain ⟨out,run⟩ := ih
    exact compileWithRoutes_accepts_tail run

/-- Every successful index identifies the exact proved attempt that emitted the
file. Legacy output retains its original compiler contract. -/
theorem compileWithRoutes_spec {routes : List ProductionLowering} {S : LinkSpec}
    {file0 : ByteArray} {cleanup : Bool} {out : RoutedOutput}
    (h : compileWithRoutes routes S file0 cleanup = .ok out) :
    (out.route = none ∧ legacyCompile (legacySpec S cleanup) file0 cleanup = .ok out.file) ∨
    ∃ i lower, out.route = some i ∧ routes[i]? = some lower ∧
      attempt lower (S.placedProductionWith lower cleanup) file0 cleanup = .ok out.file := by
  induction routes generalizing out with
  | nil =>
    cases legacy : legacyCompile (legacySpec S cleanup) file0 cleanup with
    | error message => simp [compileWithRoutes,legacy,Except.map] at h
    | ok file =>
      simp only [compileWithRoutes,legacy,Except.map] at h
      cases h
      exact .inl ⟨rfl,rfl⟩
  | cons current previous ih =>
    cases first : attempt current (S.placedProductionWith current cleanup) file0 cleanup with
    | ok file =>
      simp only [compileWithRoutes,first] at h
      cases h
      exact .inr ⟨0,current,rfl,rfl,first⟩
    | error message =>
      cases tail : compileWithRoutes previous S file0 cleanup with
      | error message => simp [compileWithRoutes,first,tail,Except.map] at h
      | ok result =>
        simp only [compileWithRoutes,first,tail,Except.map] at h
        cases h
        rcases ih tail with ⟨legacy,run⟩ | ⟨i,lower,route,index,run⟩
        · exact .inl ⟨by simp [legacy],run⟩
        · exact .inr ⟨i+1,lower,by simp [route],by simpa using index,run⟩

end Link.SemanticCompilerWith
