import FV.Concurrency.CallArgsAt

/-!
# Witness for `CallArgsAt` (#473)

The prepared code of the compiled caller of `atomic_load` passes `callUsesVirtB`
(`native_decide`, witness only); `useOps_eq` on a call `bl ld` with one argument in `x0`.
-/

namespace Concurrency.CallArgsAt.Witness

open Backend CallSeg.WitnessC

theorem usesV_fC : CallUsesVirt vcpC := (callUsesVirtB_iff _).1 (by native_decide)

/-- A direct call of `ld` with its argument `v5` in `x0` and its result `v6` from `x0`. -/
def iC : MInst := .call ⟨.sym "ld", [(.vreg 5 .int, .x 0)], [(.x 0, .vreg 6 .int)]⟩

theorem useOps_iC : ∃ ops, iC.operands = .ok ops ∧
    ops.toList.filter Operand.isUse = [⟨5, .int, .use, .early, .fixed (.x 0)⟩] :=
  ⟨_, rfl, by
    rw [useOps_eq (n := "ld") (us := [(.vreg 5 .int, .x 0)]) (ds := [(.x 0, .vreg 6 .int)])
      (by simp) (by simp) rfl]
    rfl⟩

end Concurrency.CallArgsAt.Witness
