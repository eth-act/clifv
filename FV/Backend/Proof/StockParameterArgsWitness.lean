import FV.Backend.Proof.StockParameterArgsCheck

/-! Non-vacuity of the parameter class with block arguments: a real function whose entry jumps to
a block that branches on its parameter and passes different block arguments to a return leaf and
to a trap leaf. It is outside the existing parameter class, meets the new selector and the input
checks, its source runs return and trap, its lowering is not legacy-compatible, and its actual
split code passes the check. -/

namespace Backend.Stock.ParameterArgsCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The entry doubles its parameter and jumps; block 1 branches on the value it receives and
passes it to a squaring return leaf, or passes the entry parameter to a trap leaf. -/
def function : Clif.Function := {
  name := "parameter_args_leaf"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩], term := .jump ⟨1,[1]⟩ },
    { id := 1, params := [(2,.i64)], body := [], term := .brif 2 ⟨2,[2]⟩ ⟨3,[0]⟩ },
    { id := 2, params := [(3,.i64)], body := [⟨[4],.binary .imul .i64 3 3⟩], term := .ret [4] },
    { id := 3, params := [(5,.i64)], body := [], term := .trap (.user 4) }] }

/-- The source outcome from the entry, for one argument word. -/
def sourceOutcome (word : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 12 ⟨fr,[],cm⟩)
  | _ => none

private def returns (word : BitVec 64) : Bool :=
  match sourceOutcome word with
  | some (.returned _ _) => true
  | _ => false

private def traps (word : BitVec 64) : Bool :=
  match sourceOutcome word with
  | some (.trapped (.user 4)) => true
  | _ => false

private def checks : Bool :=
  sourceOk function && !ParameterCfg.sourceOk function &&
  returns 1 && traps 0 &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => check function split.code
    | .error _ => false

-- witness: native_decide (the fixed function's selectors, input checks, source runs, lowering and split only)
private theorem checks_true : checks = true := by native_decide

theorem parameter_args_witness : Scalar.DomainAt function ∧ ParameterCfg.sourceOk function = false ∧
    ∃ result split,Stock.lower function = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      Scalar.CodeDomain function split.code := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨source,notOld⟩,_⟩,_⟩,lowered⟩ := h
  refine ⟨sourceOk_sound source,by simpa using notOld,?_⟩
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run,Bool.and_eq_true] at lowered
    obtain ⟨incompatible,rest⟩ := lowered
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => rw [splitRun] at rest; cases rest
    | ok split =>
      rw [splitRun] at rest
      exact ⟨result,split,rfl,by simpa using incompatible,splitRun,check_sound rest⟩

end Backend.Stock.ParameterArgsCfg.Fixture
