import FV.Clif.Parse
import FV.Backend.Proof.StockComparisonComputedArgsLoopCheck

/-! Non-vacuity of the loop class with computed comparisons and block arguments (#140, CB-9), on
a loop whose header compares a computed value with a register and passes block arguments:

```
function %count_to(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    jump block1(v0)

block1(v2: i64):
    v3 = iconst.i64 1
    v4 = iadd v2, v3
    v5 = icmp eq v4, v1
    brif v5, block2(v4), block1(v4)

block2(v6: i64):
    return v6
}
```

The header `block1` counts `v2` up to `v1`. Its condition compares the computed value `v4` with
the entry parameter `v1` (the CB-8 register form `subs xzr, x, y`), and both edges pass `v4`: to
the exit and back to the header. The back edge `block1 → block1` is critical, so Stock lowers it
through the edge node `edge 1 1 1`; the lowering is not legacy-compatible. The loop class with
comparison branches and block arguments (T7b-9) rejects the computed first operand, and the
computed comparison loop class (CB-8) rejects the block arguments. The new selector accepts the
function, and the checker accepts the actual split code.

The source run from `(0, 3)` returns `3` with fuel `14` and runs out of fuel with fuel `13`: the
entry jump, three passes through the 4 steps of `block1` (two back edges), and the return. -/

namespace Backend.Stock.ComparisonComputedArgsLoopCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%count_to`. -/
def countSource : String := "function %count_to(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    jump block1(v0)

block1(v2: i64):
    v3 = iconst.i64 1
    v4 = iadd v2, v3
    v5 = icmp eq v4, v1
    brif v5, block2(v4), block1(v4)

block2(v6: i64):
    return v6
}
"

/-- `%count_to` as a `Clif.Function` literal. -/
def countTo : Clif.Function := {
  name := "count_to"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64),(1,.i64)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(2,.i64)],
      body := [⟨[3],.iconst .i64 1⟩,⟨[4],.binary .iadd .i64 2 3⟩,⟨[5],.icmp .eq .i64 4 1⟩],
      term := .brif 5 ⟨2,[4]⟩ ⟨1,[4]⟩ },
    { id := 2, params := [(6,.i64)], body := [], term := .ret [6] }] }

/-- The source outcome from the entry with fuel `fuel`, for the arguments `(start, 3)`. -/
def sourceOutcome (fuel : Nat) (start : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc countTo [⟨.i64,start⟩,⟨.i64,3⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile countSource).funcs.map (·.func.toOption) = [some countTo]) &&
  (match sourceOutcome 14 0 with | some (.returned vals _) => decide (vals = [⟨.i64,3⟩]) | _ => false) &&
  (match sourceOutcome 13 0 with | some .outOfFuel => true | _ => false) &&
  sourceOk countTo && !ComparisonArgsLoopCfg.sourceOk countTo && !ComparisonComputedLoopCfg.sourceOk countTo &&
  match Stock.lower countTo with
  | .error _ => false
  | .ok result =>
    result.order.nodes.contains (.edge 1 1 1) &&
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => check countTo split.code
    | .error _ => false

-- witness: native_decide (the fixed function's parse, source runs, selectors, input checks, lowering, split and checker only)
private theorem checks_true : checks = true := by native_decide

/-- **`%count_to` is in the checked class.** The literal is the parse of the text; the selector
derives `Scalar.DomainAt`; the source run from `(0, 3)` returns `3` after `14` steps (two back
edges) and not within `13`; the T7b-9 and CB-8 loop classes reject the function; its actual
lowering has the critical-edge node of the back edge, is not legacy-compatible, and its actual
split code passes the checker, which derives the code domain. -/
theorem count_to_witness : (Clif.parseFile countSource).funcs.map (·.func.toOption) = [some countTo] ∧
    Scalar.DomainAt countTo ∧
    (∃ mem,sourceOutcome 14 0 = some (.returned [⟨.i64,3⟩] mem)) ∧
    (∃ outcome,sourceOutcome 13 0 = some outcome ∧ ∀ vals mem,outcome ≠ .returned vals mem) ∧
    ComparisonArgsLoopCfg.sourceOk countTo = false ∧ ComparisonComputedLoopCfg.sourceOk countTo = false ∧
    ∃ result split,Stock.lower countTo = .ok result ∧ Node.edge 1 1 1 ∈ result.order.nodes ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      check countTo split.code = true ∧ Scalar.CodeDomain countTo split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨parsed,returns⟩,outOfFuel⟩,source⟩,notArgs⟩,notComputed⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,source_ok_sound source,?_,?_,by simpa using notArgs,
    by simpa using notComputed,?_⟩
  · cases outcome : sourceOutcome 14 0 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases outcome : sourceOutcome 13 0 with
    | none => rw [outcome] at outOfFuel; cases outOfFuel
    | some o =>
      rw [outcome] at outOfFuel
      cases o with
      | outOfFuel => exact ⟨.outOfFuel,rfl,fun vals mem same => by cases same⟩
      | _ => cases outOfFuel
  · cases run : Stock.lower countTo with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run] at lowered
      dsimp only at lowered
      simp only [Bool.and_eq_true] at lowered
      obtain ⟨⟨edge,incompatible⟩,rest⟩ := lowered
      cases splitRun : splitEdgesChecked result.code result.edgeArgs with
      | error message => rw [splitRun] at rest; cases rest
      | ok split =>
        rw [splitRun] at rest
        exact ⟨result,split,rfl,Array.contains_iff_mem.mp edge,by simpa using incompatible,splitRun,rest,
          check_sound rest⟩

end Backend.Stock.ComparisonComputedArgsLoopCfg.Fixture
