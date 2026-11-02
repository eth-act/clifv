import FV.Clif.Parse
import FV.Backend.Proof.StockComparisonComputedArgsLoopCheck

/-! Non-vacuity of the 12-bit immediate form with a computed first operand in the loop class with
computed comparisons and block arguments (#140, CB-9), on a loop whose header compares a
computed value with a constant and passes block arguments:

```
function %count_below(i32) -> i32 {
block0(v0: i32):
    jump block1(v0)

block1(v1: i32):
    v2 = iconst.i32 1
    v3 = iadd v1, v2
    v4 = iconst.i32 10
    v5 = icmp ult v3, v4
    brif v5, block1(v3), block2(v3)

block2(v6: i32):
    return v6
}
```

The header `block1` counts up while `v1 + 1 < 10`. Its condition compares the computed value `v3`
with the encodable constant `10` (rule 5165: `subs wzr, w, #10` and `b.lo`), and both edges pass
`v3`. The back edge `block1 → block1` is critical, so Stock lowers it through the edge node
`edge 1 0 1`. The loop classes of T7b-9 and CB-8 reject the function; the new selector accepts it,
and the checker accepts the actual split code.

The source run from `0` returns `10` with fuel `52` and runs out of fuel with fuel `51`: the entry
jump, ten passes through the 5 steps of `block1` (nine back edges), and the return. -/

namespace Backend.Stock.ComparisonComputedArgsLoopCfg.ImmFixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%count_below`. -/
def countSource : String := "function %count_below(i32) -> i32 {
block0(v0: i32):
    jump block1(v0)

block1(v1: i32):
    v2 = iconst.i32 1
    v3 = iadd v1, v2
    v4 = iconst.i32 10
    v5 = icmp ult v3, v4
    brif v5, block1(v3), block2(v3)

block2(v6: i32):
    return v6
}
"

/-- `%count_below` as a `Clif.Function` literal. -/
def countBelow : Clif.Function := {
  name := "count_below"
  sig := { params := [⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(1,.i32)],
      body := [⟨[2],.iconst .i32 1⟩,⟨[3],.binary .iadd .i32 1 2⟩,⟨[4],.iconst .i32 10⟩,
        ⟨[5],.icmp .ult .i32 3 4⟩],
      term := .brif 5 ⟨1,[3]⟩ ⟨2,[3]⟩ },
    { id := 2, params := [(6,.i32)], body := [], term := .ret [6] }] }

/-- The source outcome from the entry with fuel `fuel`, for the argument `start`. -/
def sourceOutcome (fuel : Nat) (start : BitVec 32) : Option Clif.Outcome :=
  match Clif.enterFunc countBelow [⟨.i32,start⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile countSource).funcs.map (·.func.toOption) = [some countBelow]) &&
  (match sourceOutcome 52 0 with | some (.returned vals _) => decide (vals = [⟨.i32,10⟩]) | _ => false) &&
  (match sourceOutcome 51 0 with | some .outOfFuel => true | _ => false) &&
  sourceOk countBelow && !ComparisonArgsLoopCfg.sourceOk countBelow &&
  !ComparisonComputedLoopCfg.sourceOk countBelow &&
  match Stock.lower countBelow with
  | .error _ => false
  | .ok result =>
    result.order.nodes.contains (.edge 1 0 1) &&
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => check countBelow split.code
    | .error _ => false

-- witness: native_decide (the fixed function's parse, source runs, selectors, input checks, lowering, split and checker only)
private theorem checks_true : checks = true := by native_decide

/-- **`%count_below` is in the checked class.** The literal is the parse of the text; the
selector derives `Scalar.DomainAt`; the source run from `0` returns `10` after `52` steps (nine
back edges) and not within `51`; the T7b-9 and CB-8 loop classes reject the function; its actual
lowering has the critical-edge node of the back edge, is not legacy-compatible, and its actual
split code passes the checker, which derives the code domain. -/
theorem count_below_witness :
    (Clif.parseFile countSource).funcs.map (·.func.toOption) = [some countBelow] ∧
    Scalar.DomainAt countBelow ∧
    (∃ mem,sourceOutcome 52 0 = some (.returned [⟨.i32,10⟩] mem)) ∧
    (∃ outcome,sourceOutcome 51 0 = some outcome ∧ ∀ vals mem,outcome ≠ .returned vals mem) ∧
    ComparisonArgsLoopCfg.sourceOk countBelow = false ∧ ComparisonComputedLoopCfg.sourceOk countBelow = false ∧
    ∃ result split,Stock.lower countBelow = .ok result ∧ Node.edge 1 0 1 ∈ result.order.nodes ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      check countBelow split.code = true ∧ Scalar.CodeDomain countBelow split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨parsed,returns⟩,outOfFuel⟩,source⟩,notArgs⟩,notComputed⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,source_ok_sound source,?_,?_,by simpa using notArgs,
    by simpa using notComputed,?_⟩
  · cases outcome : sourceOutcome 52 0 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases outcome : sourceOutcome 51 0 with
    | none => rw [outcome] at outOfFuel; cases outOfFuel
    | some o =>
      rw [outcome] at outOfFuel
      cases o with
      | outOfFuel => exact ⟨.outOfFuel,rfl,fun vals mem same => by cases same⟩
      | _ => cases outOfFuel
  · cases run : Stock.lower countBelow with
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

end Backend.Stock.ComparisonComputedArgsLoopCfg.ImmFixture
