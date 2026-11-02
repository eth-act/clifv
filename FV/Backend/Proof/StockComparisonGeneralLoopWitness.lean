import FV.Clif.Parse
import FV.Backend.Proof.StockComparisonGeneralLoopCheck
import FV.Backend.Proof.StockComparisonGeneralSubsumption

/-! Non-vacuity of the legacy six-form loop class (#140, CB-10) on a loop whose header compares a
computed value with zero and whose branch passes no block arguments:

```
function %countdown_zero(i64) -> i64 {
block0(v0: i64):
    jump block1(v0)

block1(v1: i64):
    v2 = iconst.i64 -1
    v3 = iadd v1, v2
    v4 = iconst.i64 0
    v5 = icmp eq v3, v4
    brif v5, block3, block2

block2:
    jump block1(v3)

block3:
    return v1
}
```

The header `block1` counts down until `v1 - 1 = 0`. Its condition compares the computed value
`v3` with zero (the zero rule of `emit_icmp`: one `cbz` on `v3`), and both successors take no
arguments; the back edge `block2 → block1` is a jump with an argument. No earlier legacy class
accepts the function (`earlier_legacy_classes_reject`): the forward classes reject the back edge
or the non-parameter condition, and the loop classes of T7b-5, T7b-7 and CB-8 reject the zero form
with a computed operand. The new selector accepts it, and the checker accepts the actual unsplit
code (`sub`, `cbz`), whose per-edge vectors agree with the legacy branch arguments.

The source run from `3` takes the back edge twice and returns `1` with fuel `19`. -/

namespace Backend.Stock.ComparisonGeneralLoopCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%countdown_zero`. -/
def countdownSource : String := "function %countdown_zero(i64) -> i64 {
block0(v0: i64):
    jump block1(v0)

block1(v1: i64):
    v2 = iconst.i64 -1
    v3 = iadd v1, v2
    v4 = iconst.i64 0
    v5 = icmp eq v3, v4
    brif v5, block3, block2

block2:
    jump block1(v3)

block3:
    return v1
}
"

/-- `%countdown_zero` as a `Clif.Function` literal. -/
def countdownZero : Clif.Function := {
  name := "countdown_zero"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i64)],
      body := [⟨[2],.iconst .i64 (-1)⟩,⟨[3],.binary .iadd .i64 1 2⟩,⟨[4],.iconst .i64 0⟩,
        ⟨[5],.icmp .eq .i64 3 4⟩],
      term := .brif 5 ⟨3,[]⟩ ⟨2,[]⟩ },
    { id := 2, params := [], body := [], term := .jump ⟨1,[3]⟩ },
    { id := 3, params := [], body := [], term := .ret [1] }] }

/-- No earlier legacy (unsplit-code, empty `brif` arguments) class accepts `%countdown_zero`. -/
theorem earlier_legacy_classes_reject :
    ComparisonCfg.sourceOk countdownZero = false ∧ ComparisonImmCfg.sourceOk countdownZero = false ∧
    ComparisonZeroCfg.sourceOk countdownZero = false ∧ ConditionalCfg.sourceOk countdownZero = false ∧
    ConditionalCfg.rankedSourceOk countdownZero = false ∧ ForwardCfg.sourceOk countdownZero = false ∧
    ParameterCfg.sourceOk countdownZero = false ∧ LinearCfg.sourceOk countdownZero = false ∧
    TwoBlock.sourceOk countdownZero = false ∧ TwoBlock.Entry.sourceOk countdownZero = false ∧
    ParameterLoopCfg.sourceOk countdownZero = false ∧ ComparisonLoopCfg.sourceOk countdownZero = false ∧
    ComparisonComputedLoopCfg.sourceOk countdownZero = false := by
  decide

/-- The source outcome from the entry with fuel `fuel`, for the argument `start`. -/
def sourceOutcome (fuel : Nat) (start : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc countdownZero [⟨.i64,start⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile countdownSource).funcs.map (·.func.toOption) = [some countdownZero]) &&
  (match sourceOutcome 19 3 with | some (.returned vals _) => decide (vals = [⟨.i64,1⟩]) | _ => false) &&
  match Stock.lower countdownZero with
  | .error _ => false
  | .ok result => edgeLegacyCompatibleB result.code result.edgeArgs && check countdownZero result.code

-- witness: native_decide (the fixed function's parse, source run, lowering, compatibility check and checker only)
private theorem checks_true : checks = true := by native_decide

/-- **`%countdown_zero` is in the checked legacy six-form loop class.** The literal is the parse of
the text; the source run from `3` returns `1`; its actual unsplit lowering keeps the legacy
per-edge vectors and passes the checker, which derives `Scalar.Domain`; and no earlier legacy
class accepts the function (`earlier_legacy_classes_reject`). -/
theorem countdown_zero_witness :
    (Clif.parseFile countdownSource).funcs.map (·.func.toOption) = [some countdownZero] ∧
    Scalar.Domain countdownZero ∧
    (∃ mem,sourceOutcome 19 3 = some (.returned [⟨.i64,1⟩] mem)) ∧
    ∃ result,Stock.lower countdownZero = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = true ∧ check countdownZero result.code = true ∧
      ComparisonComputedLoopCfg.check countdownZero result.code = false := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨parsed,returns⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,?_,?_,?_⟩
  · cases run : Stock.lower countdownZero with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      simp only [Bool.and_eq_true] at lowered
      obtain ⟨result',domain,_,_⟩ := check_sound lowered.2
      exact domain
  · cases outcome : sourceOutcome 19 3 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases run : Stock.lower countdownZero with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      simp only [Bool.and_eq_true] at lowered
      refine ⟨result,rfl,lowered.1,lowered.2,?_⟩
      simp [ComparisonComputedLoopCfg.check,earlier_legacy_classes_reject.2.2.2.2.2.2.2.2.2.2.2.2]

end Backend.Stock.ComparisonGeneralLoopCfg.Fixture
