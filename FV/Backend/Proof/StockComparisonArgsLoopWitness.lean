import FV.Clif.Parse
import FV.Backend.Proof.StockComparisonArgsLoopCheck

/-! Non-vacuity of the loop class with comparison branches and block arguments (#140, T7b-9).

The witness is the first function `%f` of the Cranelift filetest
`third_party/wasmtime/cranelift/filetests/filetests/egraph/licm.clif`, unchanged:

```
function %f(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    jump block1(v0)

block1(v2: i32):
    v3 = iconst.i32 1
    v4 = iadd.i32 v1, v3
    v5 = iconst.i32 40
    v6 = icmp eq v2, v5
    v7 = iconst.i32 1
    v8 = iadd.i32 v2, v7
    brif v6, block2(v4), block1(v8)

block2(v9: i32):
    return v9
}
```

The header `block1` counts `v2` up to `40`. It branches on `icmp eq v2, v5`, a comparison of a
parameter with an encodable nonzero 12-bit constant, and passes block arguments on both edges: the
next counter back to itself and `v1 + 1` to the exit. The back edge `block1 → block1` is critical,
so Stock lowers it through the edge node `edge 1 1 1`; the lowering is not legacy-compatible. The
comparison loop class rejects the branch arguments, and the parameter loop class with block
arguments rejects the comparison condition. The new selector accepts the function, and the
checker accepts the actual split code.

The source run from `(38, 5)` returns `6` with fuel `23` and runs out of fuel with fuel `22`. One
fuel unit is one instruction or terminator, so the run executes `23 = 1 + 3 * 7 + 1` steps: the
entry jump, three passes through the 7 steps of `block1` (two back edges), and the return. -/

namespace Backend.Stock.ComparisonArgsLoopCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The text of `%f` in `egraph/licm.clif`. -/
def licmSource : String := "function %f(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    jump block1(v0)

block1(v2: i32):
    v3 = iconst.i32 1
    v4 = iadd.i32 v1, v3
    v5 = iconst.i32 40
    v6 = icmp eq v2, v5
    v7 = iconst.i32 1
    v8 = iadd.i32 v2, v7
    brif v6, block2(v4), block1(v8)

block2(v9: i32):
    return v9
}
"

/-- `%f` of `egraph/licm.clif` as a `Clif.Function` literal. -/
def licm : Clif.Function := {
  name := "f"
  sig := { params := [⟨.i32,.none,.normal⟩,⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32),(1,.i32)], body := [], term := .jump ⟨1,[0]⟩ },
    { id := 1, params := [(2,.i32)],
      body := [⟨[3],.iconst .i32 1⟩,⟨[4],.binary .iadd .i32 1 3⟩,⟨[5],.iconst .i32 40⟩,
        ⟨[6],.icmp .eq .i32 2 5⟩,⟨[7],.iconst .i32 1⟩,⟨[8],.binary .iadd .i32 2 7⟩],
      term := .brif 6 ⟨2,[4]⟩ ⟨1,[8]⟩ },
    { id := 2, params := [(9,.i32)], body := [], term := .ret [9] }] }

/-- The source outcome from the entry with fuel `fuel`, for the arguments `(start, 5)`. -/
def sourceOutcome (fuel : Nat) (start : BitVec 32) : Option Clif.Outcome :=
  match Clif.enterFunc licm [⟨.i32,start⟩,⟨.i32,5⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} fuel ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  decide ((Clif.parseFile licmSource).funcs.map (·.func.toOption) = [some licm]) &&
  (match sourceOutcome 23 38 with | some (.returned vals _) => decide (vals = [⟨.i32,6⟩]) | _ => false) &&
  (match sourceOutcome 22 38 with | some .outOfFuel => true | _ => false) &&
  sourceOk licm && !ComparisonLoopCfg.sourceOk licm && !ParameterArgsLoopCfg.sourceOk licm &&
  match Stock.lower licm with
  | .error _ => false
  | .ok result =>
    result.order.nodes.contains (.edge 1 1 1) &&
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => check licm split.code
    | .error _ => false

-- witness: native_decide (the fixed function's parse, source runs, selectors, input checks, lowering, split and checker only)
private theorem checks_true : checks = true := by native_decide

/-- **`%f` of `egraph/licm.clif` is in the checked class.** The literal is the parse of the
filetest text; the selector derives `Scalar.DomainAt`; the source run from `(38, 5)` returns `6`
after `23` steps (two back edges) and not within `22`; the comparison loop class and the parameter
loop class with block arguments reject the function; its actual lowering has the critical-edge
node of the back edge, is not legacy-compatible, and its actual split code passes the checker,
which derives the code domain. -/
theorem licm_witness : (Clif.parseFile licmSource).funcs.map (·.func.toOption) = [some licm] ∧
    Scalar.DomainAt licm ∧
    (∃ mem,sourceOutcome 23 38 = some (.returned [⟨.i32,6⟩] mem)) ∧
    (∃ outcome,sourceOutcome 22 38 = some outcome ∧ ∀ vals mem,outcome ≠ .returned vals mem) ∧
    ComparisonLoopCfg.sourceOk licm = false ∧ ParameterArgsLoopCfg.sourceOk licm = false ∧
    ∃ result split,Stock.lower licm = .ok result ∧ Node.edge 1 1 1 ∈ result.order.nodes ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      check licm split.code = true ∧ Scalar.CodeDomain licm split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨parsed,returns⟩,outOfFuel⟩,source⟩,notComparison⟩,notArgs⟩,lowered⟩ := h
  refine ⟨of_decide_eq_true parsed,source_ok_sound source,?_,?_,by simpa using notComparison,
    by simpa using notArgs,?_⟩
  · cases outcome : sourceOutcome 23 38 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases outcome : sourceOutcome 22 38 with
    | none => rw [outcome] at outOfFuel; cases outOfFuel
    | some o =>
      rw [outcome] at outOfFuel
      cases o with
      | outOfFuel => exact ⟨.outOfFuel,rfl,fun vals mem same => by cases same⟩
      | _ => cases outOfFuel
  · cases run : Stock.lower licm with
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

end Backend.Stock.ComparisonArgsLoopCfg.Fixture
