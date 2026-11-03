import FV.Backend.Proof.StockConditionalArgsRanked

/-! Non-vacuity of the ranked argument-passing class: a real function whose entry `brif` passes
different block arguments to two blocks that jump to a shared return block. It is outside the
leaf-only class, meets the ranked selector and the input checks, its source runs return on both
sides, its lowering is not legacy-compatible, and its actual split code passes the ranked check. -/

namespace Backend.Stock.ConditionalArgsCfg.RankedFixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The entry branches on its parameter; one side squares the sum it receives, the other passes
the parameter; both jump with their value to the shared return block. -/
def function : Clif.Function := {
  name := "conditional_args_ranked"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩],
      term := .brif 0 ⟨1,[1]⟩ ⟨2,[0]⟩ },
    { id := 1, params := [(2,.i64)], body := [⟨[3],.binary .imul .i64 2 2⟩], term := .jump ⟨3,[3]⟩ },
    { id := 2, params := [(4,.i64)], body := [], term := .jump ⟨3,[4]⟩ },
    { id := 3, params := [(5,.i64)], body := [], term := .ret [5] }] }

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
  rankedSourceOk function && !leafEligible function &&
  !((sigRets function.sig).any (·.purpose == .sret)) &&
  returns 1 && returns 0 &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => rankedCheck function split.code
    | .error _ => false

-- witness: native_decide (the fixed function's selectors, input checks, source runs, lowering and split only)
private theorem checks_true : checks = true := by native_decide

theorem conditional_args_ranked_witness : Scalar.DomainAt function ∧ leafEligible function = false ∧
    ∃ result split,Stock.lower function = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      Scalar.CodeDomain function split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨source,notLeaf⟩,_⟩,_⟩,_⟩,lowered⟩ := h
  refine ⟨rankedSourceOk_sound source,by simpa using notLeaf,?_⟩
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run,Bool.and_eq_true] at lowered
    obtain ⟨incompatible,rest⟩ := lowered
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => rw [splitRun] at rest; cases rest
    | ok split =>
      rw [splitRun] at rest
      exact ⟨result,split,rfl,by simpa using incompatible,splitRun,rankedCheck_sound rest⟩

end Backend.Stock.ConditionalArgsCfg.RankedFixture
