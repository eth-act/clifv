module

public import FV.Opt.Proof.RuleRestEmbed
public import FV.Opt.Proof.RuleInfraShiftAmt

@[expose] public section

/-!
# Part 1 of 2 of `RuleShifts3.lean`

`FV/Opt/Proof/RuleShifts3.lean` imports its parts (split to bound the elaboration memory of a
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

set_option maxHeartbeats 16000000 in
/-- `shifts.isle:41`. -/
theorem ok_rule_shifts_41 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_41 := by
  first | rule_auto_xr rule_shifts_41 | rule_auto_xz rule_shifts_41 | rule_auto_v rule_shifts_41

set_option maxHeartbeats 8000000 in
/-- `shifts.isle:61`. -/
theorem ok_rule_shifts_61 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_61 := by
  first | rule_auto_v rule_shifts_61 | rule_auto_w rule_shifts_61

end Opt.Proof
