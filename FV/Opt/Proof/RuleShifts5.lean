import FV.Opt.Proof.RuleRestEmbed
import FV.Opt.Proof.RuleInfraShiftAmt

/-!
# `opts/shifts.isle` (part 5): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
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
/-- `shifts.isle:152`. -/
theorem ok_rule_shifts_152 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_152 := by
  first | opt_guard rule_auto_xr rule_shifts_152 | opt_guard rule_auto_xz rule_shifts_152 |
    rule_auto_v rule_shifts_152

end Opt.Proof
