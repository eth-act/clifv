import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 4): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:254`. -/
theorem ok_rule_icmp_254 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_254 := by
  first | rule_auto_f rule_icmp_254 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_254 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_254 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_254 [tySmin_ofClif, tySmax_ofClif]

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:259`. -/
theorem ok_rule_icmp_259 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_259 := by
  first | rule_auto_f rule_icmp_259 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_259 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_259 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_259 [tySmin_ofClif, tySmax_ofClif]

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:264`. -/
theorem ok_rule_icmp_264 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_264 := by
  first | rule_auto_f rule_icmp_264 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_264 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_264 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_264 [tySmin_ofClif, tySmax_ofClif]

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:269`. -/
theorem ok_rule_icmp_269 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_269 := by
  first | rule_auto_f rule_icmp_269 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_269 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_269 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_269 [tySmin_ofClif, tySmax_ofClif]

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:274`. -/
theorem ok_rule_icmp_274 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_274 := by
  first | rule_auto_f rule_icmp_274 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_274 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_274 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_274 [tySmin_ofClif, tySmax_ofClif]

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:279`. -/
theorem ok_rule_icmp_279 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_279 := by
  rule_auto_f rule_icmp_279

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:284`. -/
theorem ok_rule_icmp_284 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_284 := by
  rule_auto_f rule_icmp_284

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:289`. -/
theorem ok_rule_icmp_289 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_289 := by
  rule_auto_f rule_icmp_289

/-- `icmp.isle:295`. -/
theorem ok_rule_icmp_295 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_295 := by
  first | rule_auto_f rule_icmp_295 | rule_auto_fi rule_icmp_295 | rule_auto_fz rule_icmp_295 | rule_auto_fiz rule_icmp_295

/-- `icmp.isle:296`. -/
theorem ok_rule_icmp_296 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_296 := by
  first | rule_auto_f rule_icmp_296 | rule_auto_fi rule_icmp_296 | rule_auto_fz rule_icmp_296 | rule_auto_fiz rule_icmp_296

/-- `icmp.isle:299`. -/
theorem ok_rule_icmp_299 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_299 := by
  first | rule_auto rule_icmp_299 | rule_auto_b rule_icmp_299 | rule_auto_i rule_icmp_299 | rule_auto_z rule_icmp_299

/-- `icmp.isle:300`. -/
theorem ok_rule_icmp_300 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_300 := by
  first | rule_auto rule_icmp_300 | rule_auto_b rule_icmp_300 | rule_auto_i rule_icmp_300 | rule_auto_z rule_icmp_300

/-- `icmp.isle:303`. -/
theorem ok_rule_icmp_303 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_303 := by
  first | rule_auto rule_icmp_303 | rule_auto_b rule_icmp_303 | rule_auto_i rule_icmp_303 | rule_auto_z rule_icmp_303

/-- `icmp.isle:304`. -/
theorem ok_rule_icmp_304 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_304 := by
  first | rule_auto rule_icmp_304 | rule_auto_b rule_icmp_304 | rule_auto_i rule_icmp_304 | rule_auto_z rule_icmp_304

/-- `icmp.isle:306`. -/
theorem ok_rule_icmp_306 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_306 := by
  first | rule_auto rule_icmp_306 | rule_auto_b rule_icmp_306 | rule_auto_i rule_icmp_306 | rule_auto_z rule_icmp_306

/-- `icmp.isle:307`. -/
theorem ok_rule_icmp_307 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_307 := by
  first | rule_auto rule_icmp_307 | rule_auto_b rule_icmp_307 | rule_auto_i rule_icmp_307 | rule_auto_z rule_icmp_307

end Opt.Proof
