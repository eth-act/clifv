import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 5): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:310`. -/
theorem ok_rule_icmp_310 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_310 := by
  first | rule_auto rule_icmp_310 | rule_auto_b rule_icmp_310 | rule_auto_i rule_icmp_310 | rule_auto_z rule_icmp_310

/-- `icmp.isle:311`. -/
theorem ok_rule_icmp_311 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_311 := by
  first | rule_auto rule_icmp_311 | rule_auto_b rule_icmp_311 | rule_auto_i rule_icmp_311 | rule_auto_z rule_icmp_311

/-- `icmp.isle:312`. -/
theorem ok_rule_icmp_312 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_312 := by
  first | rule_auto rule_icmp_312 | rule_auto_b rule_icmp_312 | rule_auto_i rule_icmp_312 | rule_auto_z rule_icmp_312

/-- `icmp.isle:313`. -/
theorem ok_rule_icmp_313 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_313 := by
  first | rule_auto rule_icmp_313 | rule_auto_b rule_icmp_313 | rule_auto_i rule_icmp_313 | rule_auto_z rule_icmp_313

/-- `icmp.isle:314`. -/
theorem ok_rule_icmp_314 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_314 := by
  first | rule_auto rule_icmp_314 | rule_auto_b rule_icmp_314 | rule_auto_i rule_icmp_314 | rule_auto_z rule_icmp_314

/-- `icmp.isle:315`. -/
theorem ok_rule_icmp_315 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_315 := by
  first | rule_auto rule_icmp_315 | rule_auto_b rule_icmp_315 | rule_auto_i rule_icmp_315 | rule_auto_z rule_icmp_315

/-- `icmp.isle:316`. -/
theorem ok_rule_icmp_316 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_316 := by
  first | rule_auto rule_icmp_316 | rule_auto_b rule_icmp_316 | rule_auto_i rule_icmp_316 | rule_auto_z rule_icmp_316

/-- `icmp.isle:317`. -/
theorem ok_rule_icmp_317 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_317 := by
  first | rule_auto rule_icmp_317 | rule_auto_b rule_icmp_317 | rule_auto_i rule_icmp_317 | rule_auto_z rule_icmp_317

/-- `icmp.isle:325`. -/
theorem ok_rule_icmp_325 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_325 := by
  first | rule_auto_e rule_icmp_325 | rule_auto_ei rule_icmp_325

/-- `icmp.isle:329`. -/
theorem ok_rule_icmp_329 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_329 := by
  first | rule_auto_e rule_icmp_329 | rule_auto_ei rule_icmp_329

/-- `icmp.isle:333`. -/
theorem ok_rule_icmp_333 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_333 := by
  first | rule_auto_e rule_icmp_333 | rule_auto_ei rule_icmp_333

/-- `icmp.isle:337`. -/
theorem ok_rule_icmp_337 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_337 := by
  first | rule_auto_e rule_icmp_337 | rule_auto_ei rule_icmp_337

/-- `icmp.isle:341`. -/
theorem ok_rule_icmp_341 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_341 := by
  first | rule_auto_e rule_icmp_341 | rule_auto_ei rule_icmp_341

/-- `icmp.isle:345`. -/
theorem ok_rule_icmp_345 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_345 := by
  first | rule_auto_e rule_icmp_345 | rule_auto_ei rule_icmp_345

/-- `icmp.isle:349`. -/
theorem ok_rule_icmp_349 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_349 := by
  first | rule_auto_e rule_icmp_349 | rule_auto_ei rule_icmp_349

/-- `icmp.isle:353`. -/
theorem ok_rule_icmp_353 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_353 := by
  first | rule_auto_e rule_icmp_353 | rule_auto_ei rule_icmp_353

end Opt.Proof
