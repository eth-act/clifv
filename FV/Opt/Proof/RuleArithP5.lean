import FV.Opt.Proof.RuleAuto
import FV.Opt.Proof.KernelBV

/-!
# Part 5 of 5 of `RuleArith.lean`

`FV/Opt/Proof/RuleArith.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `arithmetic.isle:26`. -/
theorem ok_rule_arithmetic_26 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_26 := by
  rule_auto rule_arithmetic_26

/-- `arithmetic.isle:233`. -/
theorem ok_rule_arithmetic_233 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_233 := by
  rule_auto rule_arithmetic_233

/-- `arithmetic.isle:247`. -/
theorem ok_rule_arithmetic_247 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_247 := by
  rule_auto rule_arithmetic_247

/-- `arithmetic.isle:301`. -/
theorem ok_rule_arithmetic_301 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_301 := by
  rule_auto rule_arithmetic_301

/-- `arithmetic.isle:308`. -/
theorem ok_rule_arithmetic_308 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_308 := by
  rule_auto rule_arithmetic_308

/-- `arithmetic.isle:317`. -/
theorem ok_rule_arithmetic_317 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_317 := by
  rule_auto rule_arithmetic_317

/-- `arithmetic.isle:324`. -/
theorem ok_rule_arithmetic_324 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_324 := by
  rule_auto rule_arithmetic_324

/-- `arithmetic.isle:346`. -/
theorem ok_rule_arithmetic_346 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_346 := by
  rule_auto rule_arithmetic_346

/-- `arithmetic.isle:356`. -/
theorem ok_rule_arithmetic_356 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_356 := by
  rule_auto rule_arithmetic_356

/-- `arithmetic.isle:363`. -/
theorem ok_rule_arithmetic_363 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_363 := by
  rule_auto rule_arithmetic_363

/-- `arithmetic.isle:368`. -/
theorem ok_rule_arithmetic_368 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_368 := by
  rule_auto rule_arithmetic_368

/-- `arithmetic.isle:375`. -/
theorem ok_rule_arithmetic_375 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_375 := by
  rule_auto rule_arithmetic_375

/-- `arithmetic.isle:384`. -/
theorem ok_rule_arithmetic_384 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_384 := by
  rule_auto rule_arithmetic_384

/-- `arithmetic.isle:391`. -/
theorem ok_rule_arithmetic_391 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_391 := by
  rule_auto rule_arithmetic_391

/-- `arithmetic.isle:454`. -/
theorem ok_rule_arithmetic_454 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_454 := by
  rule_auto rule_arithmetic_454

/-- `arithmetic.isle:461`. -/
theorem ok_rule_arithmetic_461 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_461 := by
  rule_auto rule_arithmetic_461

/-- `arithmetic.isle:468`. -/
theorem ok_rule_arithmetic_468 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_468 := by
  rule_auto rule_arithmetic_468

/-- `arithmetic.isle:473`. -/
theorem ok_rule_arithmetic_473 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_473 := by
  rule_auto rule_arithmetic_473

/-- `arithmetic.isle:480`. -/
theorem ok_rule_arithmetic_480 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_480 := by
  rule_auto rule_arithmetic_480

/-- `arithmetic.isle:485`. -/
theorem ok_rule_arithmetic_485 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_485 := by
  rule_auto rule_arithmetic_485

/-- `arithmetic.isle:490`. -/
theorem ok_rule_arithmetic_490 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_490 := by
  rule_auto rule_arithmetic_490

/-- `arithmetic.isle:497`. -/
theorem ok_rule_arithmetic_497 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_497 := by
  rule_auto rule_arithmetic_497

/-- `arithmetic.isle:503`. -/
theorem ok_rule_arithmetic_503 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_503 := by
  rule_auto rule_arithmetic_503

/-- `arithmetic.isle:510`. -/
theorem ok_rule_arithmetic_510 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_510 := by
  rule_auto rule_arithmetic_510

/-- `arithmetic.isle:516`. -/
theorem ok_rule_arithmetic_516 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_516 := by
  rule_auto rule_arithmetic_516

/-- `arithmetic.isle:522`. -/
theorem ok_rule_arithmetic_522 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_522 := by
  rule_auto rule_arithmetic_522

/-- `arithmetic.isle:528`. -/
theorem ok_rule_arithmetic_528 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_528 := by
  rule_auto rule_arithmetic_528

/-- `arithmetic.isle:536`. -/
theorem ok_rule_arithmetic_536 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_536 := by
  rule_auto rule_arithmetic_536

/-- `arithmetic.isle:542`. -/
theorem ok_rule_arithmetic_542 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_542 := by
  rule_auto rule_arithmetic_542

/-- `arithmetic.isle:548`. -/
theorem ok_rule_arithmetic_548 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_548 := by
  rule_auto rule_arithmetic_548

/-- `arithmetic.isle:554`. -/
theorem ok_rule_arithmetic_554 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_554 := by
  rule_auto rule_arithmetic_554

/-- `arithmetic.isle:561`. -/
theorem ok_rule_arithmetic_561 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_561 := by
  rule_auto rule_arithmetic_561

/-- `arithmetic.isle:567`. -/
theorem ok_rule_arithmetic_567 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_567 := by
  rule_auto rule_arithmetic_567

/-- `arithmetic.isle:573`. -/
theorem ok_rule_arithmetic_573 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_573 := by
  rule_auto rule_arithmetic_573

end Opt.Proof
