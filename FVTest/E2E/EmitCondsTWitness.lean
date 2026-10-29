import FVTest.E2E.FloatScopeT2
import FV.E2E.EmitCondsT

/-!
# Witnesses: the typed size and emission analyses on a float function (S11 #35)

`fW` (`FloatFinalT`: float load/const/select/store/bitcast; outside subset E) is in
`fnScopeInTB2` (`FloatScopeT2`) and its `bitcast`s keep the width (checked by `native_decide`,
witness only). `Driver.iselSzT`/`Driver.iselEmitT` then give its ISLE contracts, and
`emitCondsB_of_T2`/`emitCondsB_cleanup_of_T2` the emission conditions of its prepared VCode,
without and with the dead-code cleanup, without running `emitCondsB`.
-/

namespace EmitCondsTWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E E2E.LinkCheck FloatFinalT
  FloatScopeT2

/-- `fW` is a float function: outside subset E. -/
theorem fW_notE : Compile.functionE fW = false := by native_decide

/-- `fW`'s `bitcast`s keep the width. -/
theorem fW_bitcastWidth : bitcastWidthB fW = true := by native_decide

/-- `fW` lowers, prepares, and prepares after the cleanup; both prepared VCodes meet the literal
loads' reach `poolReachB` (#565). -/
theorem fW_pipelines : ∃ vc vcp vcq, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    prepare (prune vc) = .ok vcq ∧ poolReachB vcp = true ∧ poolReachB vcq = true := by
  have h : (match lowerFunction fW with
    | .ok vc => (match prepare vc with | .ok vcp => poolReachB vcp | .error _ => false) &&
      (match prepare (prune vc) with | .ok vcq => poolReachB vcq | .error _ => false)
    | .error _ => false) = true := by native_decide
  cases hl : lowerFunction fW with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hp : prepare vc with
    | error e => rw [hp] at h1; cases h1
    | ok vcp =>
      cases hq : prepare (prune vc) with
      | error e => rw [hq] at h2; cases h2
      | ok vcq =>
        rw [hp] at h1
        rw [hq] at h2
        exact ⟨vc, vcp, vcq, rfl, hp, hq, h1, h2⟩

/-- **`iselSzT` on `fW`.** -/
theorem fW_iselSzT : IselSzT fW :=
  let ⟨hdom, hs, hst, hsel, _, _⟩ := emitParts_of_T2 fnScopeInTB2_w
  iselSzT hdom hs hst hsel

/-- **`iselEmitT` on `fW`.** -/
theorem fW_iselEmitT : IselEmitT fW :=
  let ⟨hdom, hs, hst, hsel, hw, _⟩ := emitParts_of_T2 fnScopeInTB2_w
  iselEmitT hdom hs hst hsel hw fW_bitcastWidth

/-- **`spillSizeOkB_of_sizeOkBT` on `fW`.** -/
theorem fW_spillSize : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    spillSizeOkB vcp = true := by
  obtain ⟨vc, vcp, -, hl, hp, -, hr, -⟩ := fW_pipelines
  obtain ⟨hdom, hs, hst, hsel, -, hsz⟩ := emitParts_of_T2 fnScopeInTB2_w
  exact ⟨vc, vcp, hl, hp, spillSizeOkB_of_sizeOkBT hdom hs hst hsel hsz hl hp hr⟩

/-- **`emitConds_lowerT` / `emitCondsB_of_T2` on `fW`.** -/
theorem fW_emitConds : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    emitCondsB vcp = true := by
  obtain ⟨vc, vcp, -, hl, hp, -, hr, -⟩ := fW_pipelines
  exact ⟨vc, vcp, hl, hp, emitCondsB_of_T2 fnScopeInTB2_w fW_bitcastWidth hl hp hr⟩

/-- **`emitConds_cleanup_lowerT` / `emitCondsB_cleanup_of_T2` on `fW`.** -/
theorem fW_emitConds_cleanup : ∃ vc vcq, lowerFunction fW = .ok vc ∧ prepare (prune vc) = .ok vcq ∧
    emitCondsB vcq = true := by
  obtain ⟨vc, -, vcq, hl, -, hq, -, hr⟩ := fW_pipelines
  exact ⟨vc, vcq, hl, hq, emitCondsB_cleanup_of_T2 fnScopeInTB2_w fW_bitcastWidth hl hq hr⟩

end EmitCondsTWitness
