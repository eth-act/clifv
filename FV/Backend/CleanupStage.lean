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

end Backend
