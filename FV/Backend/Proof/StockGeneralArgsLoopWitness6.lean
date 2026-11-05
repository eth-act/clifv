import FV.Clif.Parse
import FV.Backend.Proof.StockGeneralLoopCheck6
import FV.Backend.Proof.StockGeneralSubsumption6

/-! Non-vacuity of the split loop class with `br_table` terminators (#140, CB-14c): a loop whose
header ends in a `br_table` that passes block arguments, on its back edges too.

```
function %bt2(i32) -> i32 {
block0(v0: i32):
    jump block1(v0)
block1(v1: i32):
    br_table v1, block3(v1), [block2(v1), block2(v1), block3(v1)]
block2(v2: i32):
    v3 = iconst.i32 1
    v4 = isub v2, v3
    jump block1(v4)
block3(v5: i32):
    return v5
}
```

The header `block1` ends in a `br_table` on its `i32` parameter with three table entries, each
passing `v1`; `block2` decrements the value and jumps back to the header. The table edges into
`block2` and `block3` are critical. The CB-13 split class `GeneralArgsLoopCfg5` and the new legacy
class `GeneralLoopCfg6` reject the function (`other_classes_reject`): the first has no `br_table`,
the second no `br_table` arguments. The new split selector accepts it, and its actual split code
passes the checker, which derives the code domain.
From `1` the source takes entry `block2` twice (to `0`, then to `-1`), and the index `-1` selects the
default: the run returns `-1`. -/

namespace Backend.Stock.GeneralArgsLoopCfg6.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%bt2`. -/
def tableLoopSource : String := "function %bt2(i32) -> i32 {
block0(v0: i32):
    jump block1(v0)

block1(v1: i32):
    br_table v1, block3(v1), [block2(v1), block2(v1), block3(v1)]

block2(v2: i32):
    v3 = iconst.i32 1
    v4 = isub v2, v3
    jump block1(v4)

block3(v5: i32):
    return v5
}
"

/-- `%bt2` as a `Clif.Function` literal. -/
def tableLoop : Clif.Function := {
  name := "bt2"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i32)], body := [], term := .brTable 1 ⟨3,[1]⟩ [⟨2,[1]⟩,⟨2,[1]⟩,⟨3,[1]⟩] },
    { id := 2, params := [(2,.i32)], body := [⟨[3],.iconst .i32 1⟩,⟨[4],.binary .isub .i32 2 3⟩],
      term := .jump ⟨1,[4]⟩ },
    { id := 3, params := [(5,.i32)], body := [], term := .ret [5] }] }

/-- The CB-13 split class and the new legacy class reject `%bt2`. -/
theorem other_classes_reject :
    GeneralArgsLoopCfg5.sourceOk tableLoop = false ∧ GeneralLoopCfg6.sourceOk tableLoop = false := by
  decide

/-- The source outcome of `%bt2` from the entry with fuel `fuel`, for the argument `start`. -/
def sourceOutcome (fuel : Nat) (start : BitVec 32) : Option Clif.Outcome :=
  match Clif.enterFunc tableLoop [⟨.i32,start⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile tableLoopSource).funcs.map (·.func.toOption) = [some tableLoop]) &&
  (match sourceOutcome 20 1 with | some (.returned vals _) => decide (vals = [⟨.i32,-1⟩]) | _ => false) &&
  sourceOk tableLoop &&
  match Stock.lower tableLoop with
  | .error _ => false
  | .ok result =>
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => check tableLoop split.code
    | .error _ => false

-- witness: native_decide (the fixed function's parse, source run, selector, input checks, lowering, split and checker only)
private theorem checks_true : checks = true := by native_decide -- witness: native_decide

/-- **`%bt2` (a loop header ending in a `br_table` with block arguments) is in the checked split
loop class.** The literal is the parse of the text; the selector derives `Scalar.DomainAt`; the
source run from `1` returns `-1`; the actual split code passes the checker, which derives the code
domain; the CB-13 split class and the new legacy class reject the function. -/
theorem table_loop_witness :
    (Clif.parseFile tableLoopSource).funcs.map (·.func.toOption) = [some tableLoop] ∧
    Scalar.DomainAt tableLoop ∧
    (∃ mem,sourceOutcome 20 1 = some (.returned [⟨.i32,-1⟩] mem)) ∧
    GeneralArgsLoopCfg5.sourceOk tableLoop = false ∧ GeneralLoopCfg6.sourceOk tableLoop = false ∧
    ∃ result split,Stock.lower tableLoop = .ok result ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      check tableLoop split.code = true ∧ Scalar.CodeDomain tableLoop split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨parsed,returns⟩,source⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,source_ok_sound source,?_,other_classes_reject.1,other_classes_reject.2,?_⟩
  · cases outcome : sourceOutcome 20 1 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases run : Stock.lower tableLoop with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      dsimp only at lowered
      cases splitRun : splitEdgesChecked result.code result.edgeArgs with
      | error message => rw [splitRun] at lowered; cases lowered
      | ok split =>
        rw [splitRun] at lowered
        exact ⟨result,split,rfl,splitRun,lowered,check_sound lowered⟩

end Backend.Stock.GeneralArgsLoopCfg6.Fixture
