import FV.E2E.FinalDirect
import FV.Backend.Proof.SpillLocalPipe
import FV.Backend.Proof.SpillLocalState

/-!
# Non-vacuity of the spill allocator's local facts (V4 (a), step 3)

`spillLocalOk_of_pipeline`'s premises other than the open `SpillLocalHyp` hold for
`lowerWitness`; `OpsOk` (the premise of `checkStatic_spill`, `loads_run`, `transferOp_kept`,
`transferOp_nonReg`) holds of a real instruction's operands (`movK`: a use and a reuse def).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- **Non-vacuity of `spillLocalOk_of_pipeline`**: its input premises hold for `lowerWitness`,
whose prepared code then meets `SpillLocalOk` under `SpillLocalHyp`. -/
theorem spillLocalOk_of_pipeline_witness :
    Dominated lowerWitness ∧ LowerScope lowerWitness ∧
      ∃ vc vcp, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
        (SpillLocalHyp → SpillLocalOk vcp) := by
  obtain ⟨hd, hs, vc, vcp, hl, hp, -⟩ := formsCovered_complete_witness default
  exact ⟨hd, hs, vc, vcp, hl, hp, fun hyp => spillLocalOk_of_pipeline hyp hd hs hl hp⟩

/-- **Non-vacuity of the local lemmas**: `movK` meets `SpillInstOk`; its operands meet `OpsOk`,
so the checker's static checks accept its spill locations, and its def is kept. -/
theorem spillLocal_movK_witness (c : CheckCtx) (w : String) (imm : MoveWideConst) (sz : OperandSize) :
    SpillInstOk (.movK (.vreg 1 .int) (.vreg 0 .int) imm sz) ∧
      c.checkStatic w #[⟨0, .int, .use, .early, .reg⟩, ⟨1, .int, .def, .late, .reuse 0⟩]
        (spillLocs #[⟨0, .int, .use, .early, .reg⟩, ⟨1, .int, .def, .late, .reuse 0⟩] []) [] = .ok () :=
  ⟨⟨_, rfl, opsOk_movK 0 1, fun _ h => by cases h⟩, checkStatic_spill c w (opsOk_movK 0 1)⟩

end E2E
