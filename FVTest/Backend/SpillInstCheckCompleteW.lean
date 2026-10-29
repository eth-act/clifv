module

public import FV.Backend.Proof.SpillInstCheckComplete

@[expose] public section

/-! Non-vacuity of the completeness of `spillInstOkB`/`ctlSpillB` (S11e5 Stage C, slice 8): a
`Rets` of a float vreg in v0 meets `SpillInstOk` (`spillInstOk_of_spillInstOkB`, decided), so
`spillInstOkB_of_spillInstOk` and `ctlSpillB_of` apply to it and to a one-block VCode ending in it.
`lake build FVTest.Backend.SpillInstCheckCompleteW`. -/

namespace SpillInstCheckCompleteW

open Backend Backend.Proof.Spill

/-- `rets` of a float vreg in v0. -/
def iRets : MInst := .rets [(.vreg 0 .float, .v 0)]

theorem spillInstOk_iRets : SpillInstOk iRets := spillInstOk_of_spillInstOkB (by native_decide)

/-- **Witness** of `spillInstOkB_of_spillInstOk`. -/
theorem spillInstOkB_iRets : spillInstOkB iRets = true :=
  spillInstOkB_of_spillInstOk spillInstOk_iRets

/-- A one-block VCode ending in `iRets`. -/
def vcR : VCode := { (default : VCode) with blocks := #[{ (default : VBlock) with insts := #[iRets] }] }

/-- **Witness** of `ctlSpillB_of`. -/
theorem ctlSpillB_vcR : ctlSpillB vcR = true :=
  ctlSpillB_of fun vb hvb i hi _ => by
    simp only [vcR, List.mem_singleton, List.toList_toArray] at hvb
    subst hvb
    simp only [List.mem_singleton] at hi
    subst hi
    exact spillInstOk_iRets

/-- **Witness** of `opsOkB_of_opsOk`: the operands of `iRets`. -/
theorem opsOkB_iRets : ∃ ops, iRets.operands = .ok ops ∧ opsOkB ops iRets.clobbers = true := by
  obtain ⟨ops, hops, hok, -⟩ := spillInstOk_iRets
  exact ⟨ops, hops, opsOkB_of_opsOk hok⟩

end SpillInstCheckCompleteW
