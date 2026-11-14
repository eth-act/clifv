import FV.E2E.DeadCleanupWitness
import FV.E2E.DeadCleanupFinal

/-!
# Non-vacuity of `backend_correct_final_cleanup_leaf` (#1028)

`compiledL_exists`: the compiler run of `DeadCleanupWitness.source` (a leaf), with its frame
dropped as `Backend.frameless` drops it under `preserve_frame_pointers=false`, inhabits
`CompiledCleanupL` without a frame: `AllocAF` (`AllocAF.of_frameless`), the leaf check `FnAsm.leafChk`
on its emitted code and `regArgsB` all hold, together with form coverage and `InSubset`, the
remaining premises of `backend_correct_final_cleanup_leaf` that concern the compiled function.
-/

namespace E2E.DeadCleanupLeafWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
open E2E.DeadCleanupWitness (source)

/-- Closed compilation through cleanup, allocation, `frameless false`, emission and layout. -/
def checks : Bool :=
  match lowerFunction source with
  | .error _ => false
  | .ok vc =>
    lowerCheck source vc &&
    match Backend.prepare (cleanupStage source vc) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (cleanupStage source vc) vcp && (checkAlloc vcp (spillAlloc vcp)).isOk &&
      match lowerRFunc vcp (spillAlloc vcp) with
      | .error _ => false
      | .ok af0 =>
        !(frameless false vcp af0).frame &&
        match emitFunc 0 (frameless false vcp af0) with
        | .error _ => false
        | .ok fa => fa.layout.isOk && fa.leafChk && regArgsB source.sig

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **The premise structure of `backend_correct_final_cleanup_leaf` is inhabited by a function
without a frame.** -/
theorem compiledL_exists :
    InSubset ({ funcs := [] } : Clif.Program) source ∧
    ∃ vc vcp af fa fb, CompiledCleanupL source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      af.frame = false ∧ (∀ ctx, FormsCovered ctx vcp) := by
  have h := checks_true
  simp only [checks] at h
  cases hl : lowerFunction source with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hlo, h⟩ := h
    cases hp : Backend.prepare (cleanupStage source vc) with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hpr, hck⟩, h⟩ := h
      have hc : checkAlloc vcp (spillAlloc vcp) = .ok () := by
        cases he : checkAlloc vcp (spillAlloc vcp) with
        | error e => rw [he] at hck; cases hck
        | ok u => cases u; rfl
      cases ha : lowerRFunc vcp (spillAlloc vcp) with
      | error e => rw [ha] at h; cases h
      | ok af0 =>
        rw [ha] at h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        obtain ⟨hfr, h⟩ := h
        cases he : emitFunc 0 (frameless false vcp af0) with
        | error e => rw [he] at h; cases h
        | ok fa =>
          rw [he] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hlay, hlc⟩, hra⟩ := h
          cases hb : fa.layout with
          | error e => rw [hb] at hlay; cases hlay
          | ok fb =>
            have hs := (DeadCleanupWitness.compiled_covered_exists).1
            refine ⟨hs, vc, vcp, _, fa, fb,
              ⟨hl, hlo, hp, hpr, hc, AllocAF.of_frameless false ha, fun _ => ⟨hlc, hra⟩, he, hb⟩,
              hfr, fun ctx => ?_⟩
            exact formsCovered_cleanup_complete DeadCleanupWitness.compiled_exists.2.1 hl hp ctx
