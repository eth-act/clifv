import FV.E2E.RegLevelBranch
import FV.E2E.RegLevelWrites

/-!
# Branches on the machine with their writes

`RegLevelBranch`'s `step_branchX`, `step_skipX` with `RL.GoodXW` (`GoodX` and the writes
`RL.WritesAt` of the unhooked instruction at the pc, which avoids the kept addresses `R.G`):
the branch instructions write no memory.
-/

namespace Backend.Proof

open Backend E2E

theorem step_branchXW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i : Insn} {l : Lbl}
    (hj : R.L[j]? = some (.ins i none))
    (hi : i = .b l ∨ (∃ c, i = .bcond c l) ∨ (∃ nz w r, i = .cbz nz w r l) ∨
      (∃ nz r bit, i = .tbz nz r bit l)) (hl : l ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodXW s := by
  refine ⟨step_branchX hR hj hi hl hprog hpc herr hsp, ?_⟩
  rcases hi with rfl | ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
    exact RL.writesAt_noStore hR hj hpc rfl

theorem step_skipXW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i x : Insn}
    (hj : R.L[j]? = some (.ins i none)) (hj1 : R.L[j + 1]? = some (.ins x none))
    (hi : (∃ c, i = .bcond c .skip) ∨ (∃ nz w r, i = .cbz nz w r .skip) ∨
      (∃ nz r bit, i = .tbz nz r bit .skip)) (hx : x.pairFirst = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodXW s := by
  refine ⟨step_skipX hR hj hj1 hi hx hprog hpc herr hsp, ?_⟩
  rcases hi with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ | ⟨nz, r, bit, rfl⟩ <;>
    exact RL.writesAt_noStore hR hj hpc rfl

end Backend.Proof
