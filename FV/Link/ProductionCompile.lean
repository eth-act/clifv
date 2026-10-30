import FV.Link.ProductionImage
import FV.Link.DeadCleanupCompile
import FV.Link.Placed

/-! Transactional executable compilation. The legacy layout and compiler are
retained for a failed complete Stock attempt. Output records routing data only. -/
set_option autoImplicit false
namespace Link.ProductionCompiler
open Backend E2E E2E.LinkCheck

def attempt (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  let scope := if cleanup then inScopePar S.input0 else inScopeInPar S.input0
  if !scope then .error (if cleanup then outOfScopeMsg else outOfScopeInMsg)
  else
    let I := S.inputProduction cleanup
    if okRWith (productionStage cleanup) I (I.resultsProduction cleanup) then
      leanLinkProduction S file0 cleanup
    else .error "the actual production pipeline checks failed"

structure Output where
  file : ByteArray
  stock : Bool

def legacySpec (S : LinkSpec) (cleanup : Bool) : LinkSpec :=
  if cleanup then DeadCleanup.placedPar S else S.placedPar

def legacyCompile (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  if cleanup then DeadCleanup.compileExe S file0 else compileExe S file0

def compile (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String Output :=
  match attempt (S.placedProduction cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,true⟩
  | .error _ => (legacyCompile (legacySpec S cleanup) file0 cleanup).map fun file => ⟨file,false⟩

theorem accepts_legacy {S : LinkSpec} {file0 file : ByteArray} {cleanup : Bool}
    (h : legacyCompile (legacySpec S cleanup) file0 cleanup = .ok file) :
    ∃ out, compile S file0 cleanup = .ok out := by
  unfold compile
  split
  · exact ⟨_,rfl⟩
  · exact ⟨⟨file,false⟩,by rw [h]; rfl⟩

theorem compile_spec {S : LinkSpec} {file0 : ByteArray} {cleanup : Bool} {out : Output}
    (h : compile S file0 cleanup = .ok out) :
    (out.stock = true ∧ attempt (S.placedProduction cleanup) file0 cleanup = .ok out.file) ∨
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
end Link.ProductionCompiler
