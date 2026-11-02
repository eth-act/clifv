import FV.Backend.Proof.StockParameterAnyArgsCheck

/-! Non-vacuity of the parameter class with block arguments through critical edges: the entry
passes arguments to a block that jumps to the merge block, and directly to the merge block. The
direct edge is critical, so the function is outside the all-original class; it meets the new
selector and the input checks, its source runs return on both sides, its lowering has a
critical-edge node and is not legacy-compatible, and its actual split code passes the check. -/

namespace Backend.Stock.ParameterArgsCfg.AnyFixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The entry branches on its parameter; one side squares the sum it receives and jumps to the
merge block, the other passes the parameter directly to the merge block, which returns it. -/
def function : Clif.Function := {
  name := "parameter_args_critical"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩],
      term := .brif 0 ⟨1,[1]⟩ ⟨2,[0]⟩ },
    { id := 1, params := [(2,.i64)], body := [⟨[3],.binary .imul .i64 2 2⟩], term := .jump ⟨2,[3]⟩ },
    { id := 2, params := [(4,.i64)], body := [], term := .ret [4] }] }

/-- The source outcome from the entry, for one argument word. -/
def sourceOutcome (word : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 12 ⟨fr,[],cm⟩)
  | _ => none

private def returns (word : BitVec 64) : Bool :=
  match sourceOutcome word with
  | some (.returned _ _) => true
  | _ => false

private def checks : Bool :=
  anySourceOk function && !sourceOk function && returns 1 && returns 0 &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    result.order.nodes.contains (.edge 0 1 2) &&
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => anyCheck function split.code
    | .error _ => false

-- witness: native_decide (the fixed function's selectors, input checks, source runs, lowering and split only)
private theorem checks_true : checks = true := by native_decide

theorem parameter_any_args_witness : Scalar.DomainAt function ∧ sourceOk function = false ∧
    ∃ result split,Stock.lower function = .ok result ∧ Node.edge 0 1 2 ∈ result.order.nodes ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      Scalar.CodeDomain function split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨source,notOld⟩,_⟩,_⟩,lowered⟩ := h
  refine ⟨anySourceOk_sound source,by simpa using notOld,?_⟩
  cases run : Stock.lower function with
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
      exact ⟨result,split,rfl,Array.contains_iff_mem.mp edge,by simpa using incompatible,splitRun,
        anyCheck_sound rest⟩

end Backend.Stock.ParameterArgsCfg.AnyFixture
