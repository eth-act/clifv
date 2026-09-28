import FV.Opt.Proof.RuleArith
import FV.Opt.Proof.RuleSkel
import FV.Opt.Optimize

/-!
# The proven allow-list is sound

`simplifyRulesCorrect_proven`: every `simplify` rule of `Isle.Opt.program` whose id is in
`Opt.provenSimplifyRules` is `RuleOk`. `simplifySound_proven`: the Cranelift rule set with the
`proven` allow-list is a sound rule set (`Opt.SimplifySound`), the obligation the `simplify`
pass proof takes (`Opt.Config.simplifyFn` with `ruleAllow := .proven`).

The rule list of `simplify` is only inspected through `List.filter` on rule ids (`rfl`: the
kernel reads each rule's `id` field, nothing else); the rules themselves are handled by the
per-rule theorems over an abstract program with `Data p` (`data_program`).
-/

namespace Opt.Proof

open Isle Isle.Opt

set_option maxRecDepth 20000 in
/-- The `simplify` rules in the proven allow-list. -/
theorem simplify_rules_proven :
    (program.rulesOf T.«simplify».id).filter (fun r => RuleAllow.proven.pred r.id) =
      [rule_arithmetic_8, rule_arithmetic_13, rule_arithmetic_35, rule_arithmetic_59] := by
  rfl

set_option maxRecDepth 20000 in
theorem simplify_rules_length : (program.rulesOf T.«simplify».id).length = 1281 := by
  rfl

theorem simplifyRulesCorrect_proven : SimplifyRulesCorrect program RuleAllow.proven.pred := by
  intro r hr ha
  have hm : r ∈ (program.rulesOf T.«simplify».id).filter (fun r => RuleAllow.proven.pred r.id) :=
    List.mem_filter.2 ⟨hr, ha⟩
  rw [simplify_rules_proven] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact ok_rule_arithmetic_8 data_program
  · exact ok_rule_arithmetic_13 data_program
  · exact ok_rule_arithmetic_35 data_program
  · exact ok_rule_arithmetic_59 data_program

/-- **The proven rule set is sound.** -/
theorem simplifySound_proven : SimplifySound (RuleSetId.fnWith .proven .cranelift) :=
  simplifySound _ simplifyRulesCorrect_proven (by rw [simplify_rules_length]; decide)

set_option maxRecDepth 20000 in
/-- No `simplify_skeleton` rule is in the proven allow-list. -/
theorem skeleton_rules_proven :
    (program.rulesOf T.«simplify_skeleton».id).filter (fun r => RuleAllow.proven.pred r.id) = [] := by
  rfl

set_option maxRecDepth 20000 in
theorem skeleton_rules_length : (program.rulesOf T.«simplify_skeleton».id).length = 39 := by
  rfl

theorem skeletonRulesCorrect_proven : SkeletonRulesCorrect program RuleAllow.proven.pred := by
  intro r hr ha
  have hm : r ∈ (program.rulesOf T.«simplify_skeleton».id).filter
      (fun r => RuleAllow.proven.pred r.id) := List.mem_filter.2 ⟨hr, ha⟩
  rw [skeleton_rules_proven] at hm
  cases hm

/-- **The proven skeleton rule set is sound** (the obligation `simplify`'s pass proof takes for
`Opt.Config.skeletonFn` with `ruleAllow := .proven`). -/
theorem skeletonSound_proven : SkeletonSound (RuleSetId.skeletonFnWith .proven .cranelift) :=
  skeletonSound _ skeletonRulesCorrect_proven (by rw [skeleton_rules_length]; decide)

end Opt.Proof
