import FV.Backend.Proof.StockBranchSelection
import FV.Backend.Proof.StockBranchHelperTargets

namespace Backend.Stock.Proof.BranchRootTargets
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl



private theorem branch_target (ctx : Ctx) (st : State) (l : Label) (out : V) (next : State) :
    Stock.externCtor ctx T.branch_target [.label l] st = .ok (out,next) ↔ out = .label l ∧ next = st := by
  have actual : Stock.externCtor ctx T.branch_target [.label l] st = .ok (.label l,st) := rfl
  rw [actual]
  simp [eq_comm]

/-- Both priority test-bit rules preserve the matched two-label target order,
with builder/emitter calls derived from their actual match/RHS executions. -/
theorem stock_selected_test_bit_targets {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace) (zero : Bool)
    (root : selected.rule = if zero then rule_lower_3257 else rule_lower_3251) :
    ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels := by
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  have rhs := selected.rhsRun
  rw [root,fuelEq] at matched
  rw [root] at rhs
  cases zero
  all_goals
    have hp := data_program
    cases hp
    isel_inv [*,rule_lower_3251,rule_lower_3257,sem_ctor,sem_extract,sem_unData,ext_two_targets_iff] at matched rhs
    isel_destruct
    subst_vars
    repeat (isel_inv_simp [ext_two_targets_iff] at * <;> isel_destruct <;> subst_vars)
    have envEq := ‹selected.env = _›
    have firstLabel := ‹selected.env[3]? = some (some _)›
    have secondLabel := ‹selected.env[4]? = some (some _)›
    rw [envEq] at firstLabel secondLabel
    simp at firstLabel secondLabel
    cases firstLabel
    cases secondLabel
    simp only [branch_target] at *
    isel_destruct
    subst_vars
    have emit := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    first
    | have construct := ‹ApplyInternal _ _ _ _ 46 667 _ _ _ _›
      refine BranchHelperTargets.stock_test_bit_emitted_targets rfl false ?_ ?_ construct emit <;> omega
    | have construct := ‹ApplyInternal _ _ _ _ 46 668 _ _ _ _›
      refine BranchHelperTargets.stock_test_bit_emitted_targets rfl true ?_ ?_ construct emit <;> omega

/-- The table rule derives its default-plus-table labels from its actual match
and preserves them through its actual dispatch helper. Earlier code is arbitrary. -/
theorem stock_selected_table_targets {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace)
    (root : selected.rule = rule_lower_3277) :
    ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels := by
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+20 := ⟨selected.matchFuel-20,by omega⟩
  have matched := selected.matchedRun
  have rhs := selected.rhsRun
  rw [root,fuelEq] at matched
  rw [root] at rhs
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_3277,sem_ctor,sem_extract,sem_unData,ext_jump_table_targets_iff] at matched rhs
  isel_destruct
  subst_vars
  repeat (isel_inv_simp [ext_jump_table_targets_iff] at * <;> isel_destruct <;> subst_vars)
  have envEq := ‹selected.env = _›
  have firstLabel := ‹selected.env[1]? = some (some _)›
  have secondLabel := ‹selected.env[2]? = some (some _)›
  rw [envEq] at firstLabel secondLabel
  simp at firstLabel secondLabel
  cases firstLabel
  cases secondLabel
  have dispatch := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
  refine BranchHelperTargets.stock_table_impl_targets rfl ?_ dispatch <;> omega

end Backend.Stock.Proof.BranchRootTargets
