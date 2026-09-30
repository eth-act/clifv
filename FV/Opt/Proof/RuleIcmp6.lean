import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 6): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:359`. -/
theorem ok_rule_icmp_359 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_359 := by
  first | rule_auto rule_icmp_359 | rule_auto_b rule_icmp_359 | rule_auto_i rule_icmp_359 | rule_auto_z rule_icmp_359

/-- `icmp.isle:362`. -/
theorem ok_rule_icmp_362 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_362 := by
  first | rule_auto rule_icmp_362 | rule_auto_b rule_icmp_362 | rule_auto_i rule_icmp_362 | rule_auto_z rule_icmp_362

/-- `icmp.isle:365`. -/
theorem ok_rule_icmp_365 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_365 := by
  rule_auto_f rule_icmp_365

/-- `icmp.isle:368`. -/
theorem ok_rule_icmp_368 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_368 := by
  first | rule_auto_f rule_icmp_368 | rule_auto_fi rule_icmp_368 | rule_auto_fz rule_icmp_368 | rule_auto_fiz rule_icmp_368

/-- `icmp.isle:371`. -/
theorem ok_rule_icmp_371 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_371 := by
  first | rule_auto rule_icmp_371 | rule_auto_b rule_icmp_371 | rule_auto_i rule_icmp_371 | rule_auto_z rule_icmp_371

/-- `icmp.isle:374`. -/
theorem ok_rule_icmp_374 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_374 := by
  first | rule_auto rule_icmp_374 | rule_auto_b rule_icmp_374 | rule_auto_i rule_icmp_374 | rule_auto_z rule_icmp_374

/-- `icmp.isle:377`. -/
theorem ok_rule_icmp_377 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_377 := by
  first | rule_auto rule_icmp_377 | rule_auto_b rule_icmp_377 | rule_auto_i rule_icmp_377 | rule_auto_z rule_icmp_377

/-- `icmp.isle:380`. -/
theorem ok_rule_icmp_380 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_380 := by
  first | rule_auto rule_icmp_380 | rule_auto_b rule_icmp_380 | rule_auto_i rule_icmp_380 | rule_auto_z rule_icmp_380

/-- `icmp.isle:386`. -/
theorem ok_rule_icmp_386 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_386 := by
  first | rule_auto_f rule_icmp_386 | rule_auto_fi rule_icmp_386 | rule_auto_fz rule_icmp_386 | rule_auto_fiz rule_icmp_386

/-- `icmp.isle:394`. -/
theorem ok_rule_icmp_394 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_394 := by
  first | rule_auto_f rule_icmp_394 | rule_auto_fi rule_icmp_394 | rule_auto_fz rule_icmp_394 | rule_auto_fiz rule_icmp_394

/-- `icmp.isle:402`. -/
theorem ok_rule_icmp_402 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_402 := by
  first | rule_auto_f rule_icmp_402 | rule_auto_fi rule_icmp_402 | rule_auto_fz rule_icmp_402 | rule_auto_fiz rule_icmp_402

/-- `icmp.isle:410`. -/
theorem ok_rule_icmp_410 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_410 := by
  first | rule_auto_f rule_icmp_410 | rule_auto_fi rule_icmp_410 | rule_auto_fz rule_icmp_410 | rule_auto_fiz rule_icmp_410

/-- `icmp.isle:438`. -/
theorem ok_rule_icmp_438 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_438 := by
  first | rule_auto rule_icmp_438 | rule_auto_b rule_icmp_438 | rule_auto_i rule_icmp_438 | rule_auto_z rule_icmp_438

/-- `icmp.isle:442`. -/
theorem ok_rule_icmp_442 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_442 := by
  first | rule_auto rule_icmp_442 | rule_auto_b rule_icmp_442 | rule_auto_i rule_icmp_442 | rule_auto_z rule_icmp_442

/-- `icmp.isle:447`. -/
theorem ok_rule_icmp_447 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_447 := by
  first | rule_auto rule_icmp_447 | rule_auto_b rule_icmp_447 | rule_auto_i rule_icmp_447 | rule_auto_z rule_icmp_447

/-- `icmp.isle:451`. -/
theorem ok_rule_icmp_451 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_451 := by
  first | rule_auto rule_icmp_451 | rule_auto_b rule_icmp_451 | rule_auto_i rule_icmp_451 | rule_auto_z rule_icmp_451

end Opt.Proof
