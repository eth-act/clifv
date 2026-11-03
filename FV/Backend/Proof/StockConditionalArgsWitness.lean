import FV.Backend.Proof.StockConditionalArgsDomain

/-! Non-vacuity of the argument-passing conditional class: a real function whose `brif` passes
different block arguments to a return leaf and to a trap leaf meets the selector and the source
input conditions; its source runs both return and trap; actual Stock lowering keeps nonempty
per-successor vectors (not legacy-compatible), and actual edge splitting accepts the code. -/

namespace Backend.Stock.ConditionalArgsCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- The entry branches on its parameter; the true side returns the square of the sum it
receives, the false side receives the parameter and traps. -/
def function : Clif.Function := {
  name := "conditional_args_leaves"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩],
      term := .brif 0 ⟨1,[1]⟩ ⟨2,[0]⟩ },
    { id := 1, params := [(2,.i64)], body := [⟨[3],.binary .imul .i64 2 2⟩], term := .ret [3] },
    { id := 2, params := [(4,.i64)], body := [], term := .trap (.user 3) }] }

/-- The source outcome from the entry, for one argument word. -/
def sourceOutcome (word : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc function [⟨.i64,word⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 8 ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  leafEligible function && lowerScopeB function && dominatedB function && sigAbiOk function.sig &&
  !((sigRets function.sig).any (·.purpose == .sret)) &&
  (match sourceOutcome 1 with | some (.returned _ _) => true | _ => false) &&
  (match sourceOutcome 0 with | some (.trapped (.user 3)) => true | _ => false) &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    !edgeLegacyCompatibleB result.code result.edgeArgs &&
    match splitEdgesChecked result.code result.edgeArgs with
    | .ok _ => true
    | .error _ => false

-- witness: native_decide (the fixed function's selector, input checks, source runs, lowering and split only)
private theorem checks_true : checks = true := by native_decide

theorem conditional_args_witness : Scalar.DomainAt function ∧
    (∃ vals mem,sourceOutcome 1 = some (.returned vals mem)) ∧
    sourceOutcome 0 = some (.trapped (.user 3)) ∧
    ∃ result split,Stock.lower function = .ok result ∧
      edgeLegacyCompatibleB result.code result.edgeArgs = false ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨selected,scope⟩,dominated⟩,abi⟩,ordinary⟩,returns⟩,traps⟩,lowered⟩ := h
  obtain ⟨shape⟩ := leafEligible_shape selected
  refine ⟨domainAt_of_argsLeafShape shape (lowerScope_of scope) (dominated_of dominated) abi
    (by simpa using ordinary),?_,?_,?_⟩
  · cases outcome : sourceOutcome 1 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem => exact ⟨vals,mem,rfl⟩
      | _ => cases returns
  · cases outcome : sourceOutcome 0 with
    | none => rw [outcome] at traps; cases traps
    | some o =>
      rw [outcome] at traps
      cases o with
      | trapped code =>
        cases code with
        | user n =>
          by_cases same : n = 3
          · subst same
            rfl
          · simp [same] at traps
        | _ => cases traps
      | _ => cases traps
  · cases run : Stock.lower function with
    | error message => rw [run] at lowered; cases lowered
    | ok result =>
      rw [run,Bool.and_eq_true] at lowered
      obtain ⟨incompatible,rest⟩ := lowered
      cases splitRun : splitEdgesChecked result.code result.edgeArgs with
      | error message => rw [splitRun] at rest; cases rest
      | ok split => exact ⟨result,split,rfl,by simpa using incompatible,splitRun⟩

end Backend.Stock.ConditionalArgsCfg.Fixture
