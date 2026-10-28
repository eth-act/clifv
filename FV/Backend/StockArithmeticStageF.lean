import FV.Backend.CleanupStage
import FV.Backend.Lowering.StockArithmetic

/-! The cleanup stage of the semantic (Stock arithmetic/NI) rollout routes: the production
cleanup stage `cleanupStage` (Cranelift's skip of unused instructions, then `prune`), as in
the shipped pipeline. Where the lowering validator rejects the raw output the skip does not run
and the stage is the former `Stock.Arithmetic.stage` (`stageF_of_lowerCheck_false`). -/
set_option autoImplicit false

namespace Backend.Stock.Arithmetic

def stageF (cleanup : Bool) (f : Clif.Function) (vc : VCode) : VCode :=
  if cleanup then Backend.cleanupStage f vc else vc

theorem stageF_false (f : Clif.Function) (vc : VCode) : stageF false f vc = vc := rfl

theorem stageF_true (f : Clif.Function) (vc : VCode) : stageF true f vc = cleanupStage f vc := rfl

theorem stageF_of_lowerCheck_false {cleanup : Bool} {f : Clif.Function} {vc : VCode}
    (h : Proof.Driver.lowerCheck f vc = false) : stageF cleanup f vc = stage cleanup vc := by
  cases cleanup
  · rfl
  · simp [stageF, stage, cleanupStage, skipStage, h]

/-- The stage as the routes run it: with verification off (over the validation budget) the
validator never runs, so neither does the skip (as in `cleanupStageChecked false`). -/
def stageV (verify cleanup : Bool) (f : Clif.Function) (vc : VCode) : VCode :=
  if verify then stageF cleanup f vc else stage cleanup vc

theorem stageV_true (cleanup : Bool) (f : Clif.Function) (vc : VCode) :
    stageV true cleanup f vc = stageF cleanup f vc := rfl

end Backend.Stock.Arithmetic
