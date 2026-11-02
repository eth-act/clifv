import FV.Backend.Proof.StockComparisonImmDomain

/-! Non-vacuity of the immediate comparison class: a real function whose entry
branches on `icmp slt` of its parameter and an `iconst` into a return leaf and
a trap leaf meets the selector, the source input conditions and the executable
checker; its source runs both return and trap; and the class derives the
unchanged production domain. -/

namespace Backend.Stock.ComparisonImmCfg.Fixture
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false

/-- `block0(v0: i64): v1 = iconst.i64 5; v2 = icmp slt v0, v1; brif v2, block1, block2`;
`block1` returns `v0`, `block2` traps with `user 3`. -/
def function : Clif.Function := {
  name := "comparison_imm_leaves"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.iconst .i64 5⟩,⟨[2],.icmp .slt .i64 0 1⟩],
      term := .brif 2 ⟨1,[]⟩ ⟨2,[]⟩ },
    { id := 1, params := [], body := [], term := .ret [0] },
    { id := 2, params := [], body := [], term := .trap (.user 3) }] }

/-- The source outcome from the entry, for one argument word. -/
def sourceOutcome (x : BitVec 64) : Option Clif.Outcome :=
  match Clif.enterFunc function [⟨.i64,x⟩] Clif.Mem.empty with
  | .ok (fr,cm) => some (Clif.runLoop Clif.Env.empty {funcs := []} 8 ⟨fr,[],cm⟩)
  | _ => none

private def checks : Bool :=
  leafEligible function && lowerScopeB function && dominatedB function && sigAbiOk function.sig &&
  !((sigRets function.sig).any (·.purpose == .sret)) &&
  (match sourceOutcome 3 with | some (.returned _ _) => true | _ => false) &&
  (match sourceOutcome 7 with | some (.trapped (.user 3)) => true | _ => false) &&
  match Stock.lower function with
  | .error _ => false
  | .ok result => check function result.code

-- witness: native_decide (the fixed function's selector, input checks, source runs, lowering and checker only)
private theorem checks_true : checks = true := by native_decide

theorem comparison_imm_witness : Scalar.Domain function ∧
    (∃ vals mem,sourceOutcome 3 = some (.returned vals mem)) ∧
    sourceOutcome 7 = some (.trapped (.user 3)) ∧
    ∃ result,Stock.lower function = .ok result ∧ check function result.code = true := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨selected,scope⟩,dominated⟩,abi⟩,ordinary⟩,returns⟩,traps⟩,lowered⟩ := h
  obtain ⟨shape⟩ := leafEligible_shape selected
  refine ⟨domain_of_leafShape shape (lowerScope_of scope) (dominated_of dominated) abi
    (by simpa using ordinary),?_,?_,?_⟩
  · cases outcome : sourceOutcome 3 with
    | none => rw [outcome] at returns; cases returns
    | some o =>
      rw [outcome] at returns
      cases o with
      | returned vals mem => exact ⟨vals,mem,rfl⟩
      | _ => cases returns
  · cases outcome : sourceOutcome 7 with
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
      rw [run] at lowered
      exact ⟨result,rfl,lowered⟩

end Backend.Stock.ComparisonImmCfg.Fixture
