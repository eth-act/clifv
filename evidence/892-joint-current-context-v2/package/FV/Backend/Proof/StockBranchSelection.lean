import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselGeneric
import FV.Backend.Proof.IselContract
import FV.Backend.Proof.PrepareCheck

/-! Actual selected-rule receipts from Stock named roots and retained records. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- The actual first matching rule, its rejected prefix, match/RHS executions
and final fired trace. No choice of rule is supplied by the caller. -/
structure BranchSelection (ctx : Ctx) (i : Nat) (labels : List Label) (before : State)
    (out : V) (next : State) (trace : List RuleId) where
  rule : Rule
  pre : List Rule
  post : List Rule
  candidates : program.rulesOf T.lower_branch.id = pre ++ rule :: post
  rejected : ∀ r ∈ pre, ∃ m, 999999 ≤ m + 2 + (program.rulesOf T.lower_branch.id).length ∧
    ∃ after, (matchRule program (Stock.sem ctx) {} m r [.inst i,.labels labels]).run (before, #[]) = .ok (none, after)
  matchFuel : Nat
  env : Isle.Interp.Env V
  matched : State
  matchTrace : Array RuleId
  rhsTrace : Array RuleId
  fuelBound : 999999 ≤ matchFuel + 2 + (program.rulesOf T.lower_branch.id).length
  matchedRun : (matchRule program (Stock.sem ctx) {} matchFuel rule [.inst i,.labels labels]).run (before, #[]) =
    .ok (some env, matched, matchTrace)
  rhsRun : (evalExpr program (Stock.sem ctx) {} 999999 rule.rhs env).run (matched, matchTrace) =
    .ok (some out, next, rhsTrace)
  fired : trace = (rhsTrace.push rule.id).toList

/-- A successful actual named lower call supplies complete first-match
selection receipts through the existing generic interpreter inversion. -/
theorem stock_named_branch_selection {ctx : Ctx} {i : Nat} {labels : List Label} {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out, next, trace)) :
    Nonempty (BranchSelection ctx i labels before out next trace) := by
  unfold Stock.runTerm Interp.run at run
  rw [program_termByName_lower_branch] at run
  dsimp only at run
  cases call : (applyTerm program (Stock.sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id [.inst i,.labels labels]).run
      (before, #[]) with
  | error e => rw [call] at run; cases run
  | ok q =>
    obtain ⟨v, after, fired⟩ := q
    rw [call] at run
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    obtain ⟨r, pre, post, candidates, rejected, fuel, env, middle, final, rhsTrace,
      fuelBound, matchedRun, rhsRun, stateEq⟩ :=
      applyTerm_internal_some_first (p := program) (sem := Stock.sem ctx) (cfg := {}) rfl
        data_program.t687 rfl rfl (n := 999999) call
    have finalEq := congrArg Prod.fst stateEq
    have traceEq := congrArg Prod.snd stateEq
    change after = final at finalEq
    subst final
    exact ⟨⟨r, pre, post, candidates, rejected, fuel, env, middle.1, middle.2, rhsTrace,
      fuelBound, matchedRun, rhsRun, congrArg Array.toList traceEq⟩⟩


end Backend.Stock.Proof
