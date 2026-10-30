import FV.Backend.Proof.PerEdgeSpillCycleFixture

namespace Backend.Stock.Proof.SharedJumpFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.IndexedSpillFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

/-- Cached actual cyclic-source terminator and both live loop-value classes. -/
def Layout (p : EdgeVCode) : Prop :=
  p.code.blocks[3]!.insts = #[.jump 1] ∧
  p.code.classes[194]? = some .int ∧ p.code.classes[195]? = some .int
instance (p : EdgeVCode) : Decidable (Layout p) := by unfold Layout; infer_instance
private def view : Except String Bool := do
  let result ← Stock.lower function
  let p ← prepareAt result.code result.edgeArgs
  pure (decide (Layout p))
private theorem observed : view.toOption = some true := by decide +kernel

/-- Recover the cached layout from the actual complete Stock preparation,
without reevaluating the complete source pipeline in downstream proofs. -/
theorem shared_jump_layout {result : Result} {p : EdgeVCode}
    (run : Stock.lower function = .ok result) (raw : prepareAt result.code result.edgeArgs = .ok p) : Layout p := by
  have actual := observed
  unfold view at actual
  rw [run] at actual
  simp only [bind,Except.bind] at actual
  rw [raw] at actual
  simpa only [bind,Except.bind,pure,Except.pure,Except.toOption,Option.some.injEq,decide_eq_true_eq] using actual

end Backend.Stock.Proof.SharedJumpFixture
