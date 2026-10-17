import FV.Opt.Proof.RuleExtEmbed
import FV.Opt.Proof.RuleInfraShiftAmt
import FV.Opt.Proof.RuleIntRetry

/-!
# `opts/shifts.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleIntSplit.lean`, `RuleIntRetry.lean`); a `first` chain lists the
templates the rule was checked against, in order. Rules making `iconst_u`/`iconst_s` at a type
variable split it on `isInt` (`rule_auto_xzi`, `rule_auto_zi`): at a float type the constant
has no rule.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

-- In this module `kbv` first tries `kbv_amt` (`RuleInfraShiftAmt.lean`) on the isolated goal, under
-- `kbv_guard` (a failure, also a runtime exception, falls through to the general search).
open Lean Elab Tactic in
local elab_rules : tactic
  | `(tactic| kbv) => Opt.Proof.KernelBV.isolate (do evalTactic (← `(tactic| kbv_guard 200000 kbv_amt)))

set_option maxHeartbeats 4000000


/-- `shifts.isle:140`. -/
theorem ok_rule_shifts_140 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_140 := by
  rule_auto_cat rule_shifts_140

/-- `shifts.isle:141`. -/
theorem ok_rule_shifts_141 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_141 := by
  rule_auto_cat rule_shifts_141

/-- `shifts.isle:142`. -/
theorem ok_rule_shifts_142 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_142 := by
  rule_auto_cat rule_shifts_142

/-- `shifts.isle:143`. -/
theorem ok_rule_shifts_143 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_143 := by
  rule_auto_cat rule_shifts_143

/-- `shifts.isle:204`. -/
theorem ok_rule_shifts_204 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_204 := by
  first | rule_auto rule_shifts_204 | rule_auto_b rule_shifts_204 | rule_auto_i rule_shifts_204 | rule_auto_z rule_shifts_204

/-- `shifts.isle:205`. -/
theorem ok_rule_shifts_205 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_205 := by
  first | rule_auto rule_shifts_205 | rule_auto_b rule_shifts_205 | rule_auto_i rule_shifts_205 | rule_auto_z rule_shifts_205

/-- `shifts.isle:297`. -/
theorem ok_rule_shifts_297 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_297 := by
  rule_auto_xzi rule_shifts_297

/-- `shifts.isle:300`. -/
theorem ok_rule_shifts_300 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_300 := by
  rule_auto_xzi rule_shifts_300

/-- `shifts.isle:303`. -/
theorem ok_rule_shifts_303 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_303 := by
  rule_auto_xzi rule_shifts_303

/-- `shifts.isle:306`. -/
theorem ok_rule_shifts_306 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_306 := by
  rule_auto_xzi rule_shifts_306

/-- `shifts.isle:309`. -/
theorem ok_rule_shifts_309 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_309 := by
  rule_auto_xzi rule_shifts_309

/-- `shifts.isle:313`. -/
theorem ok_rule_shifts_313 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_313 := by
  first | rule_auto rule_shifts_313 | rule_auto_b rule_shifts_313 | rule_auto_i rule_shifts_313 | rule_auto_z rule_shifts_313

/-- `shifts.isle:314`. -/
theorem ok_rule_shifts_314 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_314 := by
  first | rule_auto rule_shifts_314 | rule_auto_b rule_shifts_314 | rule_auto_i rule_shifts_314 | rule_auto_z rule_shifts_314

/-- `shifts.isle:316`. -/
theorem ok_rule_shifts_316 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_316 := by
  first | rule_auto rule_shifts_316 | rule_auto_b rule_shifts_316 | rule_auto_i rule_shifts_316 | rule_auto_z rule_shifts_316

/-- `shifts.isle:318`. -/
theorem ok_rule_shifts_318 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_318 := by
  first | rule_auto rule_shifts_318 | rule_auto_b rule_shifts_318 | rule_auto_i rule_shifts_318 | rule_auto_z rule_shifts_318

/-- `shifts.isle:319`. -/
theorem ok_rule_shifts_319 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_319 := by
  first | rule_auto rule_shifts_319 | rule_auto_b rule_shifts_319 | rule_auto_i rule_shifts_319 | rule_auto_z rule_shifts_319

/-- `shifts.isle:322`. -/
theorem ok_rule_shifts_322 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_322 := by
  rule_auto_zi rule_shifts_322

/-- `shifts.isle:323`. -/
theorem ok_rule_shifts_323 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_323 := by
  rule_auto_zi rule_shifts_323

/-- `shifts.isle:324`. -/
theorem ok_rule_shifts_324 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_324 := by
  rule_auto_zi rule_shifts_324

/-- `shifts.isle:325`. -/
theorem ok_rule_shifts_325 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_325 := by
  rule_auto_zi rule_shifts_325

/-- `shifts.isle:326`. -/
theorem ok_rule_shifts_326 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_326 := by
  rule_auto_zi rule_shifts_326

/-- `shifts.isle:329`. -/
theorem ok_rule_shifts_329 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_329 := by
  rule_auto_zi rule_shifts_329

/-- `shifts.isle:330`. -/
theorem ok_rule_shifts_330 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_330 := by
  rule_auto_zi rule_shifts_330

/-- `shifts.isle:331`. -/
theorem ok_rule_shifts_331 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_331 := by
  rule_auto_zi rule_shifts_331

end Opt.Proof
