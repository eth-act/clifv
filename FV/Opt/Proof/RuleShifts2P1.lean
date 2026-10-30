import FV.Opt.Proof.RuleExtEmbed
import FV.Opt.Proof.RuleInfraShiftAmt
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntRetry

/-!
# Part 1 of 3 of `RuleShifts2.lean`

`FV/Opt/Proof/RuleShifts2.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
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

/-- `shifts.isle:143`. -/
theorem ok_rule_shifts_143 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_143 := by
  rule_auto_cat rule_shifts_143

/-- `shifts.isle:297`. -/
theorem ok_rule_shifts_297 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_297 := by
  rule_auto_xzi rule_shifts_297

/-- `shifts.isle:306`. -/
theorem ok_rule_shifts_306 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_306 := by
  rule_auto_xzi rule_shifts_306

/-- `shifts.isle:314`. -/
theorem ok_rule_shifts_314 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_314 := by
  first | rule_auto rule_shifts_314 | rule_auto_b rule_shifts_314 | rule_auto_i rule_shifts_314 | rule_auto_z rule_shifts_314

/-- `shifts.isle:319`. -/
theorem ok_rule_shifts_319 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_319 := by
  first | rule_auto rule_shifts_319 | rule_auto_b rule_shifts_319 | rule_auto_i rule_shifts_319 | rule_auto_z rule_shifts_319

/-- `shifts.isle:324`. -/
theorem ok_rule_shifts_324 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_324 := by
  rule_auto_zi rule_shifts_324

/-- `shifts.isle:329`. -/
theorem ok_rule_shifts_329 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_329 := by
  rule_auto_zi rule_shifts_329

end Opt.Proof
