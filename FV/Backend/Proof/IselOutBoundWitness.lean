module

public import FV.Backend.Proof.IselOutBoundRun

@[expose] public section

/-!
# Witness: `lowerFunction_outgoing_le` is tight on a call with stack arguments (S10g, #404)

`source` calls the extern `g10` with ten `i64` arguments: two go on the stack, 16 bytes
(`stackBytes`). `checks_true` (`native_decide`) decides `lowerScopeB`, `outBoundLe 16`, and
that `lowerFunction` succeeds with an outgoing area of exactly 16 bytes; so
`lowerFunction_outgoing_le` applies with the bound 16 and the bound is reached.
-/

namespace Backend.Proof.OutBound.Witness

open Backend Backend.Proof Backend.Proof.Driver

/-- `(i64 × 10) -> i64 system_v`. -/
def sig10 : Clif.Signature :=
  { params := (List.range 10).map fun _ => { ty := .i64 }, returns := [{ ty := .i64 }],
    callConv := some .systemV }

/-- `v10 = call g10(v0, …, v9); return v10`. -/
def source : Clif.Function :=
  { name := "ob", sig := sig10, externs := [(0, { name := "g10", sig := sig10 })],
    blocks := [
      { id := 0, params := (List.range 10).map fun v => (v, .i64),
        body := [{ results := [10], inst := .call 0 (List.range 10) }],
        term := .ret [10] }] }

/-- The compiler's output (the default is never used: `checks_true`). -/
def vc : VCode := (lowerFunction source).toOption.getD default

/-- The decidable facts. -/
def checks : Bool :=
  lowerScopeB source && outBoundLe 16 source &&
    (match lowerFunction source with
     | .ok v => v.outgoing == 16
     | .error _ => false) &&
    (stackBytes sig10 == 16)

theorem checks_true : checks = true := by native_decide

/-- **`lowerFunction_outgoing_le` applies to `source` with the bound 16, which is reached.** -/
theorem outgoing_le_applies : vc.outgoing ≤ 16 ∧ vc.outgoing = 16 := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hs, hob⟩, hl⟩, -⟩ := h
  split at hl
  · rename_i v hv
    have hvc : vc = v := by rw [vc, hv]; rfl
    rw [hvc]
    exact ⟨lowerFunction_outgoing_le (lowerScope_of hs) hob hv, by simpa using hl⟩
  · cases hl

end Backend.Proof.OutBound.Witness
