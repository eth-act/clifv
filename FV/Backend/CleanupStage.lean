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

section
open Proof.Driver

/-- `skipStage` as the compiler runs it (`skipStage_eq_impl`, `@[csimp]`, #877): `lowerCheck` and
`skipDead` both begin with the same lowering (`buildCtx`, `lowBlocks`), which `skipStage` ran
twice; here it runs once and both read it (`skipDead`'s part is `skipDeadImpl`'s). -/
def skipStageImpl (f : Clif.Function) (vc : VCode) : VCode :=
  if Compile.functionE f then
    match buildCtx f with
    | .error _ => vc
    | .ok (ctx, _, st0) =>
      match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
          f.blocks.length with
      | none => vc
      | some bl =>
        let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
        if shapeOk f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f ctx gn) && brIdxOk f ctx &&
            ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) &&
            (callsStackOkB f vc.outgoing && entryOkB f) then
          let R := renOf gn
          let tbl := skipDropSet f R bl vc
          let mask := skipMask f R bl vc (skipAt f fun b j => tbl.contains (b, j))
          if deleteCheck vc mask then deleteWith vc mask else vc
        else vc
  else vc

@[csimp] theorem skipStage_eq_impl : @skipStage = @skipStageImpl := by
  funext f vc
  unfold skipStage skipStageImpl lowerCheck skipDead
  cases Compile.functionE f
  · simp
  · simp only [Bool.true_and, ↓reduceIte]
    cases buildCtx f with
    | error e => simp
    | ok r =>
      obtain ⟨ctx, _, st0⟩ := r
      simp only
      cases lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
          f.blocks.length with
      | none => simp
      | some bl => rfl

end

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
