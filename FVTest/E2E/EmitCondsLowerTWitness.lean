import FVTest.E2E.FloatFinalT
import FV.Backend.Proof.IselEmitTDriver
import FV.E2E.EmitCondsLowerT

/-!
# Witnesses: the typed emission analysis on a float function (S11 #35)

`FloatDriverT.fW` (float `load`/`f64const`/`select`/`store`/`bitcast`; outside subset E) meets the
premises of `Driver.iselEmitT` (decided by `native_decide`, witness only; `LowerScopeT` is
`FloatFinalT.scopeT_w`), so `IselEmitT fW` holds, and `E2E.emitParts_lowerT` /
`E2E.emitParts_cleanup_lowerT` give the emission facts of its prepared code without running
`emitCondsB`.
-/

namespace EmitCondsLowerTWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E FloatDriverT FloatFinalT

/-- `fW` is outside subset E. -/
theorem fW_not_E : Compile.functionE fW = false := by native_decide

theorem dominated_w : dominatedB fW = true := by native_decide
theorem storeTyped_w : Compile.storeTypedB fW = true := by native_decide
theorem selectTyped_w : Compile.selectTypedB fW = true := by native_decide
theorem extendsWiden_w : extendsWidenB fW = true := by native_decide

/-- **`bitcastWidthB` holds on `fW`** (its `bitcast.i64` of an `f64`). -/
theorem bitcastWidth_w : bitcastWidthB fW = true := by native_decide

/-- **`iselEmitT` on a float function.** -/
theorem iselEmitT_w : IselEmitT fW :=
  iselEmitT dominated_w scopeT_w storeTyped_w selectTyped_w extendsWiden_w bitcastWidth_w

/-- **`emitParts_lowerT` on a float function.** -/
theorem emitParts_lowerT_w :
    immsOkB (vcpOf fW) = true ∧ (vcpOf fW).noAlwaysB = true ∧ branchTargetsOkB (vcpOf fW) = true :=
  E2E.emitParts_lowerT dominated_w scopeT_w iselEmitT_w lowerFunction_w prepare_w

/-- **`emitParts_cleanup_lowerT` on a float function.** -/
theorem emitParts_cleanup_lowerT_w : ∃ vcp, Backend.prepare (prune (vcOf fW)) = .ok vcp ∧
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have h : (Backend.prepare (prune (vcOf fW))).toBool = true := by native_decide
  cases hp : Backend.prepare (prune (vcOf fW)) with
  | error e => rw [hp] at h; cases h
  | ok vcp =>
    exact ⟨vcp, rfl, E2E.emitParts_cleanup_lowerT dominated_w scopeT_w iselEmitT_w lowerFunction_w hp⟩

end EmitCondsLowerTWitness
