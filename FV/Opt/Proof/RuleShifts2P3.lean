import FV.Opt.Proof.RuleExtEmbed
import FV.Opt.Proof.RuleInfraShiftAmt
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntRetry

/-!
# Part 3 of 3 of `RuleShifts2.lean`

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

/-- `shifts.isle:142`. -/
theorem ok_rule_shifts_142 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_142 := by
  rule_auto_cat rule_shifts_142

/-- `shifts.isle:205`. -/
theorem ok_rule_shifts_205 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_205 := by
  first | rule_auto rule_shifts_205 | rule_auto_b rule_shifts_205 | rule_auto_i rule_shifts_205 | rule_auto_z rule_shifts_205

/-- `shifts.isle:303`. -/
theorem ok_rule_shifts_303 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_303 := by
  rule_auto_xzi rule_shifts_303

/-- `shifts.isle:313`. -/
theorem ok_rule_shifts_313 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_313 := by
  first | rule_auto rule_shifts_313 | rule_auto_b rule_shifts_313 | rule_auto_i rule_shifts_313 | rule_auto_z rule_shifts_313

/-- `shifts.isle:318`. -/
theorem ok_rule_shifts_318 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_318 := by
  first | rule_auto rule_shifts_318 | rule_auto_b rule_shifts_318 | rule_auto_i rule_shifts_318 | rule_auto_z rule_shifts_318

/-- `shifts.isle:323`. -/
theorem ok_rule_shifts_323 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_323 := by
  rule_auto_zi rule_shifts_323

/-- `shifts.isle:326`. -/
theorem ok_rule_shifts_326 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_326 := by
  rule_auto_zi rule_shifts_326

/-- `shifts.isle:331`. -/
theorem ok_rule_shifts_331 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_331 := by
  rule_auto_zi rule_shifts_331

end Opt.Proof
