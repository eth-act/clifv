import FV.Clif.MemTrap

/-!
# A `notrap` load never traps and keeps the memory (#970)

The justification of the stock-configured driver's drop of unused `notrap` loads
(`StockConfig.dropDeadNotrapLoads`, `FVTest/Backend/StockConfig.lean`). That pass is not proved
and is outside `backend_correct`; this lemma states the CLIF fact it relies on.
-/

namespace Clif

/-- **A `notrap` load reads without changing the memory, or it is stuck; it never traps.**
This justifies dropping a `notrap` load whose result is unused in the stock-configured driver
(`StockConfig.dropDeadNotrapLoads`, #970): the source run either continues past the load with the
same memory (`.ok ([v], cm)`; its value `v` is unused), or it is `stuck` there (out of bounds, a
misaligned `aligned` access or an uninitialised read, `Mem.checkAccess`), which the backend
theorems do not constrain (`E2E.ArmRefines` of a `.stuck` outcome is `True`). A load whose flags
have a trap code traps out of bounds (`Mem.checkAccess`); dropping it is not justified here. -/
theorem evalInst_notrap_load (fr : Frame) (cm : Mem) (op : LoadOp) (ty : Ty) (fl : MemFlags)
    (p : ValueId) (off : Int) (hn : fl.trapCode = none) :
    (∃ v, evalInst fr cm (.load op ty fl p off) = .ok ([v], cm)) ∨
      ∃ m, evalInst fr cm (.load op ty fl p off) = .stuck m := by
  cases h : evalInst fr cm (.load op ty fl p off) with
  | ok r =>
    left
    simp only [evalInst] at h
    cases hg : fr.get p <;>
      simp only [hg, Res.ok_bind, Res.trap_bind, Res.stuck_bind, reduceCtorEq] at h
    rename_i pv
    cases hc : Res.check (op.size ty ≤ ty.bytes) "load: access wider than result" <;>
      simp only [hc, Res.ok_bind, Res.trap_bind, Res.stuck_bind, reduceCtorEq] at h
    cases hl : cm.load fl (effAddr pv off) (op.size ty) (8 * op.size ty) <;>
      simp only [hl, Res.ok_bind, Res.trap_bind, Res.stuck_bind, Res.pure_eq, reduceCtorEq] at h
    cases h
    exact ⟨_, rfl⟩
  | trap c => exact absurd h (evalInst_notrap (fl := fl) rfl hn c)
  | stuck m => exact .inr ⟨m, rfl⟩

end Clif
