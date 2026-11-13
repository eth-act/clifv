import FVTest.E2E.FloatScopeT2
import FV.E2E.EmitCondsT

/-!
# Witnesses: the typed size and emission analyses on a float function (S11 #35)

`fW` (`FloatFinalT`: float load/const/select/store/bitcast; outside subset E) is in
`fnScopeInTB2` (`FloatScopeT2`) and its `bitcast`s keep the width (checked by `native_decide`,
witness only). `Driver.iselSzT`/`Driver.iselEmitT` then give its ISLE contracts, and
`emitCondsB_of_T2`/`emitCondsB_cleanup_of_T2` the emission conditions of its prepared VCode,
without and with the dead-code cleanup, without running `emitCondsB`.

`fW` has an `f64const` (`fW_f64const`), lowered to an `fmov d, #imm` (`fW_const_code`). The
literal loads' reach of its prepared VCodes is the theorem `poolReachB_lowerT` /
`poolReachB_cleanup_lowerT` (#1002, `fW_poolReach`: no literal-pool load, not checked by
running), so the size and emission theorems apply to it without a premise on the pool.
-/

namespace EmitCondsTWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E E2E.LinkCheck FloatFinalT
  FloatScopeT2

/-- `fW` is a float function: outside subset E. -/
theorem fW_notE : Compile.functionE fW = false := by native_decide

/-- `fW`'s `bitcast`s keep the width. -/
theorem fW_bitcastWidth : bitcastWidthB fW = true := by native_decide

/-- `fW` lowers, prepares, and prepares after the cleanup. -/
theorem fW_pipelines : ∃ vc vcp vcq, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    prepare (prune vc) = .ok vcq := by
  have h : (match lowerFunction fW with
    | .ok vc => (prepare vc).toBool && (prepare (prune vc)).toBool
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
      | ok vcq => exact ⟨vc, vcp, vcq, rfl, hp, hq⟩

/-- `fW` has an `f64const`, whose bits need no literal pool (`Compile.f64PoolFree`). -/
theorem fW_f64const : (fW.blocks.any fun B => B.body.any fun s =>
    match s.inst with
    | .iconst ty imm => ty == .f64 && Compile.f64PoolFree imm.toNat
    | _ => false) = true := by native_decide

/-- The `f64const` of `fW` is lowered to an `fmov d, #imm` (`constant_f64`'s rule 3), and the
prepared code has no literal-pool load (checked by running: witness only). -/
theorem fW_const_code : ((vcpOf fW).blocks.any fun vb => vb.insts.any fun i =>
    match i with
    | .fpuMoveFPImm _ _ _ => true
    | _ => false) = true ∧ (vcpOf fW).noPoolB = true := by native_decide

/-- **`noPoolB_lowerT` / `poolReachB_lowerT` and their cleanup forms on `fW`** (#1002): the
prepared VCodes of a typed function with an `f64const` have no literal-pool load and meet the
literal loads' reach, by the theorems (the scope `LowerScopeT` from `fnScopeInTB2`). -/
theorem fW_poolReach : ∃ vc vcp vcq, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    prepare (prune vc) = .ok vcq ∧ vcp.noPoolB = true ∧ poolReachB vcp = true ∧
    vcq.noPoolB = true ∧ poolReachB vcq = true := by
  obtain ⟨vc, vcp, vcq, hl, hp, hq⟩ := fW_pipelines
  obtain ⟨-, hs, -, -, -, -⟩ := emitParts_of_T2 fnScopeInTB2_w
  exact ⟨vc, vcp, vcq, hl, hp, hq, noPoolB_lowerT hs hl hp, poolReachB_lowerT hs hl hp,
    noPoolB_cleanup_lowerT hs hl hq, poolReachB_cleanup_lowerT hs hl hq⟩

/-- **`formsCovered2_completeT` on `fW`** (#1002): its prepared VCode's coverage is two-way. -/
theorem fW_covered2 : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    FormsCovered2 vcp := by
  obtain ⟨vc, vcp, -, hl, hp, -⟩ := fW_pipelines
  obtain ⟨hdom, hs, hst, hsel, -, -⟩ := emitParts_of_T2 fnScopeInTB2_w
  exact ⟨vc, vcp, hl, hp, formsCovered2_completeT hdom hs hst hsel hl hp⟩

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
  obtain ⟨vc, vcp, -, hl, hp, -⟩ := fW_pipelines
  obtain ⟨hdom, hs, hst, hsel, -, hsz⟩ := emitParts_of_T2 fnScopeInTB2_w
  exact ⟨vc, vcp, hl, hp, spillSizeOkB_of_sizeOkBT hdom hs hst hsel hsz hl hp⟩

/-- **`emitConds_lowerT` / `emitCondsB_of_T2` on `fW`.** -/
theorem fW_emitConds : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    emitCondsB vcp = true := by
  obtain ⟨vc, vcp, -, hl, hp, -⟩ := fW_pipelines
  exact ⟨vc, vcp, hl, hp, emitCondsB_of_T2 fnScopeInTB2_w fW_bitcastWidth hl hp⟩

/-- **`emitConds_cleanup_lowerT` / `emitCondsB_cleanup_of_T2` on `fW`.** -/
theorem fW_emitConds_cleanup : ∃ vc vcq, lowerFunction fW = .ok vc ∧ prepare (prune vc) = .ok vcq ∧
    emitCondsB vcq = true := by
  obtain ⟨vc, -, vcq, hl, -, hq⟩ := fW_pipelines
  exact ⟨vc, vcq, hl, hq, emitCondsB_cleanup_of_T2 fnScopeInTB2_w fW_bitcastWidth hl hq⟩

end EmitCondsTWitness
