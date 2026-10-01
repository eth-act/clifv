import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/remat.isle`: proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `remat.isle:4`. -/
theorem ok_rule_remat_4 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_4 := by
  first | rule_auto rule_remat_4 | rule_auto_xr rule_remat_4

set_option maxHeartbeats 4000000 in
/-- `remat.isle:6`. -/
theorem ok_rule_remat_6 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_6 := by
  first | rule_auto rule_remat_6 | rule_auto_xr rule_remat_6

set_option maxHeartbeats 4000000 in
/-- `remat.isle:8`. -/
theorem ok_rule_remat_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_8 := by
  first | rule_auto rule_remat_8 | rule_auto_xr rule_remat_8

set_option maxHeartbeats 4000000 in
/-- `remat.isle:10`. -/
theorem ok_rule_remat_10 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_10 := by
  first | rule_auto rule_remat_10 | rule_auto_xr rule_remat_10

set_option maxHeartbeats 4000000 in
/-- `remat.isle:12`. -/
theorem ok_rule_remat_12 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_12 := by
  first | rule_auto rule_remat_12 | rule_auto_xr rule_remat_12

set_option maxHeartbeats 4000000 in
/-- `remat.isle:14`. -/
theorem ok_rule_remat_14 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_14 := by
  first | rule_auto rule_remat_14 | rule_auto_xr rule_remat_14

set_option maxHeartbeats 4000000 in
/-- `remat.isle:16`. -/
theorem ok_rule_remat_16 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_16 := by
  first | rule_auto rule_remat_16 | rule_auto_xr rule_remat_16

set_option maxHeartbeats 4000000 in
/-- `remat.isle:18`. -/
theorem ok_rule_remat_18 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_18 := by
  first | rule_auto rule_remat_18 | rule_auto_xr rule_remat_18

set_option maxHeartbeats 4000000 in
/-- `remat.isle:20`. -/
theorem ok_rule_remat_20 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_20 := by
  first | rule_auto rule_remat_20 | rule_auto_xr rule_remat_20

set_option maxHeartbeats 4000000 in
/-- `remat.isle:22`. -/
theorem ok_rule_remat_22 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_22 := by
  first | rule_auto rule_remat_22 | rule_auto_xr rule_remat_22

set_option maxHeartbeats 4000000 in
/-- `remat.isle:24`. -/
theorem ok_rule_remat_24 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_24 := by
  first | rule_auto rule_remat_24 | rule_auto_xr rule_remat_24

set_option maxHeartbeats 4000000 in
/-- `remat.isle:26`. -/
theorem ok_rule_remat_26 {p : Isle.Program} (hd : Data p) : RuleOk p rule_remat_26 := by
  first | rule_auto rule_remat_26 | rule_auto_xr rule_remat_26

end Opt.Proof
