import FV.E2E.RegLevelBranch
import FV.E2E.RegLevelWrites

/-!
# Branches on the machine with their writes (A3, #412, slice F8b)

`RegLevelBranch`'s `step_branchX` and `step_skipX` with `RL.GoodXW` (`GoodX` and the writes
`RL.WritesAt` of the unhooked instruction at the pc, which avoids the kept addresses `R.G`):
the branch instructions write no memory.
-/

namespace Backend.Proof

open Backend E2E

/-- **A branch line's state** with the body's `sp` and its writes: `GoodXW` (the step goes to the
target label or the next line, and the branch instruction writes no memory). -/
theorem step_branchXW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i : Insn} {l : Lbl}
    (hj : R.L[j]? = some (.ins i none))
    (hi : i = .b l ∨ (∃ c, i = .bcond c l) ∨ (∃ nz w r, i = .cbz nz w r l) ∨
      (∃ nz r bit, i = .tbz nz r bit l)) (hl : l ≠ .skip)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodXW s :=
  ⟨step_branchX hR hj hi hl hprog hpc herr hsp,
    RL.writesAt_noStore hR hj hpc (by rcases hi with rfl | ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ |
      ⟨nz, r, bit, rfl⟩ <;> rfl)⟩

/-- **The inverted short branch of a relaxed branch** with the body's `sp` and its writes:
`GoodXW` (the step goes past the next line, which is not the first word of an `adrp` pair, or to
it, and the branch instruction writes no memory). -/
theorem step_skipXW {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i x : Insn}
    (hj : R.L[j]? = some (.ins i none)) (hj1 : R.L[j + 1]? = some (.ins x none))
    (hi : (∃ c, i = .bcond c .skip) ∨ (∃ nz w r, i = .cbz nz w r .skip) ∨
      (∃ nz r bit, i = .tbz nz r bit .skip)) (hx : x.pairFirst = false)
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) (hsp : spOf s = R.spB) : R.GoodXW s :=
  ⟨step_skipX hR hj hj1 hi hx hprog hpc herr hsp,
    RL.writesAt_noStore hR hj hpc (by rcases hi with ⟨c, rfl⟩ | ⟨nz, w, r, rfl⟩ |
      ⟨nz, r, bit, rfl⟩ <;> rfl)⟩

end Backend.Proof
