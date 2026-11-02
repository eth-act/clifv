import FV.Backend.Proof.StockConditionalTargets
import FV.Backend.Proof.StockBranchSelection

namespace Backend.Stock.Proof.ConditionalRoots
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl


/-- The ordinary brif rule derives its builder and emitter calls from its actual
match and RHS executions. The selected rule identifies this internal case,
without imposing a new source acceptance condition. -/
theorem stock_selected_brif_targets {ctx : Ctx} {i : Nat} {labels : List Label}
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace)
    (root : selected.rule = rule_lower_3231) :
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
  isel_inv [*,rule_lower_3231,sem_ctor,sem_extract,sem_unData,ext_two_targets_iff] at matched rhs
  isel_destruct
  subst_vars
  repeat (isel_inv_simp [ext_two_targets_iff] at * <;> isel_destruct <;> subst_vars)
  have envEq := ‹selected.env = _›
  have firstLabel := ‹selected.env[1]? = some (some _)›
  have secondLabel := ‹selected.env[2]? = some (some _)›
  rw [envEq] at firstLabel secondLabel
  simp at firstLabel secondLabel
  cases firstLabel
  cases secondLabel
  have construct := ‹ApplyInternal _ _ _ _ 46 722 _ _ _ _›
  have emit := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  refine ConditionalTargets.stock_conditional_emitted_targets rfl ?_ ?_ construct emit <;> omega

end Backend.Stock.Proof.ConditionalRoots
