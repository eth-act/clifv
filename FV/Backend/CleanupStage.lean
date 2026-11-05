import FV.Backend.SkipDead
import FV.Backend.DeadCleanup
import FV.Compile.Subset

/-!
# The production cleanup stage

Between the lowering (validated by `lowerCheck` on its unchanged output) and `prepare`, the
production compiler runs, as Cranelift does:

* `skipStage`: Cranelift's skip of unused instructions (`skipDead`, `FV/Backend/SkipDead.lean`),
  on a function of subset E whose lowering the validator accepts (the proof of `skipDead` needs
  `lowerCheck`); any other function is left unchanged;
* `DeadCleanup.prune`: the conservative dead-producer cleanup.
-/

namespace Backend

/-- Cranelift's skip of unused instructions, where its proof applies (subset E, `lowerCheck`). -/
def skipStage (f : Clif.Function) (vc : VCode) : VCode :=
  if Compile.functionE f && Proof.Driver.lowerCheck f vc then Proof.Driver.skipDead f vc else vc

/-- **The production cleanup stage**: `skipStage`, then `DeadCleanup.prune`. -/
def cleanupStage (f : Clif.Function) (vc : VCode) : VCode :=
  DeadCleanup.prune (skipStage f vc)

/-- **The cleanup stage as the compiler runs it**, reusing the lowering validator's verdict
instead of running `lowerCheck` a second time: `checked` says the driver's validation of this `vc`
passed (`lowerCheckFor`, which is `lowerCheck` on subset E). Without a verdict (verification off,
e.g. over the validation budget) the skip does not run, so `lowerCheck` never runs outside the
budget; with one it is `cleanupStage` (`cleanupStageChecked_true`). -/
def cleanupStageChecked (checked : Bool) (f : Clif.Function) (vc : VCode) : VCode :=
  DeadCleanup.prune (if checked && Compile.functionE f then Proof.Driver.skipDead f vc else vc)

theorem cleanupStageChecked_true {f : Clif.Function} {vc : VCode}
    (h : Compile.functionE f = true → Proof.Driver.lowerCheck f vc = true) :
    cleanupStageChecked true f vc = cleanupStage f vc := by
  unfold cleanupStageChecked cleanupStage skipStage
  cases hE : Compile.functionE f
  · simp
  · simp [h hE]

/-- With the verdict of `lowerCheck` itself (whatever it is), the checked stage is the stage. -/
theorem cleanupStageChecked_lowerCheck (f : Clif.Function) (vc : VCode) :
    cleanupStageChecked (Proof.Driver.lowerCheck f vc) f vc = cleanupStage f vc := by
  unfold cleanupStageChecked cleanupStage skipStage
  cases Proof.Driver.lowerCheck f vc <;> cases Compile.functionE f <;> simp

end Backend
