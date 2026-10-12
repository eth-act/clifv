import FV.Backend.Proof.DeadCleanupCorrect
import FV.Backend.Proof.DeadCleanupSem

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Driver

private def witnessVC : VCode :=
  ⟨"cleanup_return", #[⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩
private def mvnOps : Array Operand :=
  #[⟨2, .int, .def, .late, .reg⟩, ⟨1, .int, .use, .early, .reg⟩]
private def bicOps : Array Operand :=
  #[⟨3, .int, .def, .late, .reg⟩, ⟨0, .int, .use, .early, .reg⟩,
    ⟨1, .int, .use, .early, .reg⟩]
private def returnOps : Array Operand := #[⟨3, .int, .use, .early, .fixed (.x 0)⟩]
private def rho0 : Nat → CV := fun _ => 0#128
private def rho1 := vdefUpd mvnOps [ofX (~~~(0#64))] rho0
private def rho2 := vdefUpd bicOps [0#128] rho1

private theorem witnessTerminated : ∀ vb ∈ witnessVC.blocks.toList,
    ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true := by
  intro vb hb
  simp only [witnessVC, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst vb
  exact ⟨liveReturn, rfl, rfl⟩

/-- Non-vacuity for the simulation and return-preservation chain: the original
VCode really executes the deleted instruction, then returns a live result. -/
example (w : Arm.ArmState) :
    E2E.VReturns witnessVC (mspec 0) rho0 w [(.vreg 3 .int, .x 0)] [0#128] w ∧
    E2E.VReturns (clean witnessVC) (mspec 0) rho0 w
      [(.vreg 3 .int, .x 0)] [0#128] w := by
  have h : E2E.VReturns witnessVC (mspec 0) rho0 w
      [(.vreg 3 .int, .x 0)] [0#128] w := by
    refine ⟨0, 2, rho2, w, witnessVC.blocks[0]!, returnOps, [], ?_,
      rfl, rfl, rfl, rfl, rfl⟩
    have h1 : VStep witnessVC (mspec 0) (.run ⟨0, 0, rho0, w⟩)
        (.run ⟨0, 1, rho1, w⟩) :=
      VStep.step rfl rfl (show deadMvn.operands = .ok mvnOps from rfl)
        rfl rfl (VNext.next (by decide))
    have h2 : VStep witnessVC (mspec 0) (.run ⟨0, 1, rho1, w⟩)
        (.run ⟨0, 2, rho2, w⟩) :=
      VStep.step rfl rfl (show liveBic.operands = .ok bicOps from rfl)
        rfl rfl (VNext.next (by decide))
    exact .step h1 (.step h2 (.refl _))
  exact ⟨h, returns_clean (fun _ _ _ _ _ _ hp hs => mspec_pure hp hs) witnessTerminated h⟩

/-- Non-vacuity for trap preservation: a real `udf` is retained and remains
observable after its dead pure prefix is removed. -/
example (w : Arm.ArmState) : ∃ vc : VCode,
    E2E.VTraps vc (mspec 0) rho0 w .intOvf ∧
    E2E.VTraps (clean vc) (mspec 0) rho0 w .intOvf := by
  let trap : MInst := .udf .intOvf
  let vc : VCode := ⟨"cleanup_trap", #[⟨0, #[deadMvn, trap], #[], #[]⟩],
    #[.int, .int, .int], 0, 0, #[]⟩
  have ht : ∀ vb ∈ vc.blocks.toList,
      ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true := by
    intro vb hb
    simp only [vc, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst vb
    exact ⟨trap, rfl, rfl⟩
  have h : E2E.VTraps vc (mspec 0) rho0 w .intOvf := by
    refine ⟨0, 1, rho1, w, vc.blocks[0]!, trap, #[], [], w, ?_,
      rfl, rfl, rfl, rfl, rfl⟩
    exact .step (VStep.step rfl rfl (show deadMvn.operands = .ok mvnOps from rfl)
      rfl rfl (VNext.next (by decide))) (.refl _)
  exact ⟨vc, h, traps_clean (fun _ _ _ _ _ _ hp hs => mspec_pure hp hs) ht h⟩

end Backend.DeadCleanup
