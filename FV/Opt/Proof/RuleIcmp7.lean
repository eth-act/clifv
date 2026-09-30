import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 7): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:479`. -/
theorem ok_rule_icmp_479 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_479 := by
  first | rule_auto rule_icmp_479 | rule_auto_b rule_icmp_479 | rule_auto_i rule_icmp_479 | rule_auto_z rule_icmp_479

/-- `icmp.isle:482`. -/
theorem ok_rule_icmp_482 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_482 := by
  first | rule_auto rule_icmp_482 | rule_auto_b rule_icmp_482 | rule_auto_i rule_icmp_482 | rule_auto_z rule_icmp_482

/-- `icmp.isle:485`. -/
theorem ok_rule_icmp_485 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_485 := by
  first | rule_auto rule_icmp_485 | rule_auto_b rule_icmp_485 | rule_auto_i rule_icmp_485 | rule_auto_z rule_icmp_485

/-- `icmp.isle:486`. -/
theorem ok_rule_icmp_486 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_486 := by
  first | rule_auto rule_icmp_486 | rule_auto_b rule_icmp_486 | rule_auto_i rule_icmp_486 | rule_auto_z rule_icmp_486

/-- `icmp.isle:489`. -/
theorem ok_rule_icmp_489 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_489 := by
  first | rule_auto rule_icmp_489 | rule_auto_b rule_icmp_489 | rule_auto_i rule_icmp_489 | rule_auto_z rule_icmp_489

/-- `icmp.isle:490`. -/
theorem ok_rule_icmp_490 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_490 := by
  first | rule_auto rule_icmp_490 | rule_auto_b rule_icmp_490 | rule_auto_i rule_icmp_490 | rule_auto_z rule_icmp_490

/-- `icmp.isle:491`. -/
theorem ok_rule_icmp_491 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_491 := by
  first | rule_auto rule_icmp_491 | rule_auto_b rule_icmp_491 | rule_auto_i rule_icmp_491 | rule_auto_z rule_icmp_491

/-- `icmp.isle:492`. -/
theorem ok_rule_icmp_492 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_492 := by
  first | rule_auto rule_icmp_492 | rule_auto_b rule_icmp_492 | rule_auto_i rule_icmp_492 | rule_auto_z rule_icmp_492

/-- `icmp.isle:495`. -/
theorem ok_rule_icmp_495 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_495 := by
  first | rule_auto rule_icmp_495 | rule_auto_b rule_icmp_495 | rule_auto_i rule_icmp_495 | rule_auto_z rule_icmp_495

/-- `icmp.isle:498`. -/
theorem ok_rule_icmp_498 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_498 := by
  first | rule_auto rule_icmp_498 | rule_auto_b rule_icmp_498 | rule_auto_i rule_icmp_498 | rule_auto_z rule_icmp_498

/-- `icmp.isle:501`. -/
theorem ok_rule_icmp_501 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_501 := by
  first | rule_auto rule_icmp_501 | rule_auto_b rule_icmp_501 | rule_auto_i rule_icmp_501 | rule_auto_z rule_icmp_501

/-- `icmp.isle:502`. -/
theorem ok_rule_icmp_502 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_502 := by
  first | rule_auto rule_icmp_502 | rule_auto_b rule_icmp_502 | rule_auto_i rule_icmp_502 | rule_auto_z rule_icmp_502

/-- `icmp.isle:505`. -/
theorem ok_rule_icmp_505 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_505 := by
  first | rule_auto rule_icmp_505 | rule_auto_b rule_icmp_505 | rule_auto_i rule_icmp_505 | rule_auto_z rule_icmp_505

/-- `icmp.isle:506`. -/
theorem ok_rule_icmp_506 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_506 := by
  first | rule_auto rule_icmp_506 | rule_auto_b rule_icmp_506 | rule_auto_i rule_icmp_506 | rule_auto_z rule_icmp_506

/-- `icmp.isle:509`. -/
theorem ok_rule_icmp_509 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_509 := by
  first | rule_auto rule_icmp_509 | rule_auto_b rule_icmp_509 | rule_auto_i rule_icmp_509 | rule_auto_z rule_icmp_509

/-- `icmp.isle:510`. -/
theorem ok_rule_icmp_510 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_510 := by
  first | rule_auto rule_icmp_510 | rule_auto_b rule_icmp_510 | rule_auto_i rule_icmp_510 | rule_auto_z rule_icmp_510

end Opt.Proof
