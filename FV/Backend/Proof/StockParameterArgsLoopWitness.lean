import FV.Backend.Proof.StockParameterArgsLoopCheck

/-! Non-vacuity of the loop class with block arguments on parameter branches (#140, T7b-8).

A counting self loop: the header `block1(v2, v3)` adds its counter `v2` to the sum `v3`,
decrements the counter, and branches on its counter parameter, passing the new counter and sum
back to itself and the sum to the exit block. In CLIF:

```
function %countdown(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 0
    jump block1(v0, v1)
block1(v2: i64, v3: i64):
    v4 = iadd v3, v2
    v5 = iconst.i64 -1
    v6 = iadd v2, v5
    brif v2, block1(v6, v4), block2(v4)
block2(v7: i64):
    return v7
}
```

The back edge `block1 → block1` is critical, so Stock lowers it through the edge node
`edge 1 0 1`, which holds the copies; the lowering is not legacy-compatible. The loop parameter
class rejects the branch arguments and the forward class with block arguments rejects the back
edge. The new selector accepts the function, the checker accepts the actual split code, and the
source run from `3` takes the back edge three times and returns `3 + 2 + 1 = 6`. -/

namespace Backend.Stock.ParameterArgsLoopCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The counting self loop `%countdown` above. -/
def countdown : Clif.Function := {
  name := "countdown"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.iconst .i64 0⟩], term := .jump ⟨1,[0,1]⟩ },
    { id := 1, params := [(2,.i64),(3,.i64)],
      body := [⟨[4],.binary .iadd .i64 3 2⟩,⟨[5],.iconst .i64 (-1)⟩,⟨[6],.binary .iadd .i64 2 5⟩],
      term := .brif 2 ⟨1,[6,4]⟩ ⟨2,[4]⟩ },
    { id := 2, params := [(7,.i64)], body := [], term := .ret [7] }] }

/-- The source outcome from the entry, for one argument word. -/
def sourceOutcome (word : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc countdown [⟨.i64,word⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 32 ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  (match sourceOutcome 3 with | some (.returned vals _) => decide (vals = [⟨.i64,6⟩]) | _ => false) &&
  sourceOk countdown && !ParameterLoopCfg.sourceOk countdown && !ParameterArgsCfg.anySourceOk countdown &&
  match Stock.lower countdown with
  | .error _ => false
  | .ok result =>
    result.order.nodes.contains (.edge 1 0 1) &&
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => check countdown split.code
    | .error _ => false

-- witness: native_decide (the fixed function's source run, selectors, input checks, lowering, split and checker only)
private theorem checks_true : checks = true := by native_decide

/-- **The counting self loop is in the checked class.** The selector derives `Scalar.DomainAt`;
the source run from `3` returns `6` through the back edge; both earlier classes reject the
function; its actual lowering has the critical-edge node of the back edge, is not
legacy-compatible, and its actual split code passes the checker, which derives the code domain. -/
theorem countdown_witness : Scalar.DomainAt countdown ∧
    (∃ mem,sourceOutcome 3 = some (.returned [⟨.i64,6⟩] mem)) ∧
    ParameterLoopCfg.sourceOk countdown = false ∧ ParameterArgsCfg.anySourceOk countdown = false ∧
    ∃ result split,Stock.lower countdown = .ok result ∧ Node.edge 1 0 1 ∈ result.order.nodes ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      check countdown split.code = true ∧ Scalar.CodeDomain countdown split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨returns,source⟩,notLoop⟩,notForward⟩,lowered⟩ := h
  refine ⟨source_ok_sound source,?_,by simpa using notLoop,by simpa using notForward,?_⟩
  · cases outcome : sourceOutcome 3 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem =>
        simp only [decide_eq_true_eq] at returns
        exact ⟨mem,by rw [returns]⟩
      | _ => cases returns
  · cases run : Stock.lower countdown with
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

end Backend.Stock.ParameterArgsLoopCfg.Fixture
