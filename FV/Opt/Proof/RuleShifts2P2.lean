import FV.Opt.Proof.RuleExtEmbed
import FV.Opt.Proof.RuleInfraShiftAmt
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntRetry

/-!
# Part 2 of 3 of `RuleShifts2.lean`

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

/-- `shifts.isle:141`. -/
theorem ok_rule_shifts_141 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_141 := by
  rule_auto_cat rule_shifts_141

/-- `shifts.isle:204`. -/
theorem ok_rule_shifts_204 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_204 := by
  first | rule_auto rule_shifts_204 | rule_auto_b rule_shifts_204 | rule_auto_i rule_shifts_204 | rule_auto_z rule_shifts_204

/-- `shifts.isle:300`. -/
theorem ok_rule_shifts_300 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_300 := by
  rule_auto_xzi rule_shifts_300

/-- `shifts.isle:309`. -/
theorem ok_rule_shifts_309 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_309 := by
  rule_auto_xzi rule_shifts_309

/-- `shifts.isle:316`. -/
theorem ok_rule_shifts_316 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_316 := by
  first | rule_auto rule_shifts_316 | rule_auto_b rule_shifts_316 | rule_auto_i rule_shifts_316 | rule_auto_z rule_shifts_316

/-- `shifts.isle:322`. -/
theorem ok_rule_shifts_322 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_322 := by
  rule_auto_zi rule_shifts_322

/-- `shifts.isle:325`. -/
theorem ok_rule_shifts_325 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_325 := by
  rule_auto_zi rule_shifts_325

/-- `shifts.isle:330`. -/
theorem ok_rule_shifts_330 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_330 := by
  rule_auto_zi rule_shifts_330

end Opt.Proof
