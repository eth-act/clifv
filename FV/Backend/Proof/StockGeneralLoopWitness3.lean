import FV.Clif.Parse
import FV.Backend.Proof.StockGeneralLoopCheck3
import FV.Backend.Proof.StockGeneralSubsumption3

/-! Non-vacuity of the legacy loop class with plain `i8` conditions (#140, CB-12) on a loop whose
header branches on a computed `i8` value and whose branch passes no block arguments:

```
function %countdown_narrow(i8) -> i8 {
block0(v0: i8):
    jump block1(v0)

block1(v1: i8):
    v2 = iconst.i8 -1
    v3 = iadd v1, v2
    brif v3, block2, block3

block2:
    jump block1(v3)

block3:
    return v1
}
```

The header `block1` counts down until `v1 - 1 = 0`. Its condition is the computed `i8` value `v3`
itself: the lowering is `add w, w, #255`, `tst w, #0xff` and `b.ne` (`lower_brif` 3231,
`is_nonzero` 4988). The back edge `block2 → block1` is a jump with an argument. The CB-11 legacy
class `GeneralLoopCfg2` and the CB-11 split class `GeneralArgsLoopCfg2` reject the function
(`earlier_classes_reject`): an `i8` value is not one of their conditions. The new selector accepts
it, and the checker accepts the actual unsplit code, whose per-edge vectors agree with the legacy
branch arguments.

The source run from `3` takes the back edge twice and returns `1` with fuel `13`. -/

namespace Backend.Stock.GeneralLoopCfg3.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%countdown_narrow`. -/
def countdownSource : String := "function %countdown_narrow(i8) -> i8 {
block0(v0: i8):
    jump block1(v0)

block1(v1: i8):
    v2 = iconst.i8 -1
    v3 = iadd v1, v2
    brif v3, block2, block3

block2:
    jump block1(v3)

block3:
    return v1
}
"

/-- `%countdown_narrow` as a `Clif.Function` literal. -/
def countdownNarrow : Clif.Function := {
  name := "countdown_narrow"
  sig := { params := [⟨.i8,.none,.normal⟩], returns := [⟨.i8,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i8)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i8)],
      body := [⟨[2],.iconst .i8 (-1)⟩,⟨[3],.binary .iadd .i8 1 2⟩],
      term := .brif 3 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [], body := [], term := .jump ⟨1,[3]⟩ },
    { id := 3, params := [], body := [], term := .ret [1] }] }

/-- The CB-11 legacy and split classes reject `%countdown_narrow`; its condition is a narrow
condition of the CB-12 classes. -/
theorem earlier_classes_reject :
    GeneralLoopCfg2.sourceOk countdownNarrow = false ∧
    GeneralArgsLoopCfg2.sourceOk countdownNarrow = false ∧
    GeneralArgsLoopCfg3.narrowEligible countdownNarrow 3 = true := by
  decide

/-- The source outcome from the entry with fuel `fuel`, for the argument `start`. -/
def sourceOutcome (fuel : Nat) (start : BitVec 8) : Option Clif.Outcome :=
  match Clif.enterFunc countdownNarrow [⟨.i8,start⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile countdownSource).funcs.map (·.func.toOption) = [some countdownNarrow]) &&
  (match sourceOutcome 13 3 with | some (.returned vals _) => decide (vals = [⟨.i8,1⟩]) | _ => false) &&
  match Stock.lower countdownNarrow with
  | .error _ => false
  | .ok result => edgeLegacyCompatibleB result.code result.edgeArgs && check countdownNarrow result.code

-- witness: native_decide (the fixed function's parse, source run, lowering, compatibility check and checker only)
private theorem checks_true : checks = true := by native_decide

/-- **`%countdown_narrow` is in the checked legacy loop class with plain `i8` conditions.** The
literal is the parse of the text; the source run from `3` returns `1`; its actual unsplit lowering
keeps the legacy per-edge vectors and passes the checker, which derives `Scalar.Domain`; and the
CB-11 legacy checker rejects it (`earlier_classes_reject`). -/
theorem countdown_narrow_witness :
    (Clif.parseFile countdownSource).funcs.map (·.func.toOption) = [some countdownNarrow] ∧
    Scalar.Domain countdownNarrow ∧
    (∃ mem,sourceOutcome 13 3 = some (.returned [⟨.i8,1⟩] mem)) ∧
    ∃ result,Stock.lower countdownNarrow = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check countdownNarrow result.code = true ∧
      GeneralLoopCfg2.check countdownNarrow result.code = false := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨parsed,returns⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,?_,?_,?_⟩
  · cases run : Stock.lower countdownNarrow with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      simp only [Bool.and_eq_true] at lowered
      obtain ⟨result',domain,_,_⟩ := check_sound lowered.2
      exact domain
  · cases outcome : sourceOutcome 13 3 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases run : Stock.lower countdownNarrow with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      simp only [Bool.and_eq_true] at lowered
      refine ⟨result,rfl,lowered.1,lowered.2,?_⟩
      simp [GeneralLoopCfg2.check,earlier_classes_reject.1]

end Backend.Stock.GeneralLoopCfg3.Fixture
