import FV.Opt.Proof.RuleAuto
import FV.Opt.Proof.KernelBV

/-!
# Part 3 of 5 of `RuleArith.lean`

`FV/Opt/Proof/RuleArith.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `arithmetic.isle:18`. -/
theorem ok_rule_arithmetic_18 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_18 := by
  rule_auto rule_arithmetic_18

/-- `arithmetic.isle:35`. -/
theorem ok_rule_arithmetic_35 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_35 := by
  rule_auto rule_arithmetic_35

/-- `arithmetic.isle:243`. -/
theorem ok_rule_arithmetic_243 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_243 := by
  rule_auto rule_arithmetic_243

/-- `arithmetic.isle:297`. -/
theorem ok_rule_arithmetic_297 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_297 := by
  rule_auto rule_arithmetic_297

/-- `arithmetic.isle:304`. -/
theorem ok_rule_arithmetic_304 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_304 := by
  rule_auto rule_arithmetic_304

/-- `arithmetic.isle:313`. -/
theorem ok_rule_arithmetic_313 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_313 := by
  rule_auto rule_arithmetic_313

/-- `arithmetic.isle:320`. -/
theorem ok_rule_arithmetic_320 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_320 := by
  rule_auto rule_arithmetic_320

/-- `arithmetic.isle:339`. -/
theorem ok_rule_arithmetic_339 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_339 := by
  rule_auto rule_arithmetic_339

/-- `arithmetic.isle:354`. -/
theorem ok_rule_arithmetic_354 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_354 := by
  rule_auto rule_arithmetic_354

/-- `arithmetic.isle:359`. -/
theorem ok_rule_arithmetic_359 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_359 := by
  rule_auto rule_arithmetic_359

/-- `arithmetic.isle:366`. -/
theorem ok_rule_arithmetic_366 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_366 := by
  rule_auto rule_arithmetic_366

/-- `arithmetic.isle:373`. -/
theorem ok_rule_arithmetic_373 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_373 := by
  rule_auto rule_arithmetic_373

/-- `arithmetic.isle:380`. -/
theorem ok_rule_arithmetic_380 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_380 := by
  rule_auto rule_arithmetic_380

/-- `arithmetic.isle:389`. -/
theorem ok_rule_arithmetic_389 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_389 := by
  rule_auto rule_arithmetic_389

/-- `arithmetic.isle:452`. -/
theorem ok_rule_arithmetic_452 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_452 := by
  rule_auto rule_arithmetic_452

/-- `arithmetic.isle:459`. -/
theorem ok_rule_arithmetic_459 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_459 := by
  rule_auto rule_arithmetic_459

/-- `arithmetic.isle:464`. -/
theorem ok_rule_arithmetic_464 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_464 := by
  rule_auto rule_arithmetic_464

/-- `arithmetic.isle:471`. -/
theorem ok_rule_arithmetic_471 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_471 := by
  rule_auto rule_arithmetic_471

/-- `arithmetic.isle:478`. -/
theorem ok_rule_arithmetic_478 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_478 := by
  rule_auto rule_arithmetic_478

/-- `arithmetic.isle:483`. -/
theorem ok_rule_arithmetic_483 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_483 := by
  rule_auto rule_arithmetic_483

/-- `arithmetic.isle:488`. -/
theorem ok_rule_arithmetic_488 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_488 := by
  rule_auto rule_arithmetic_488

/-- `arithmetic.isle:495`. -/
theorem ok_rule_arithmetic_495 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_495 := by
  rule_auto rule_arithmetic_495

/-- `arithmetic.isle:501`. -/
theorem ok_rule_arithmetic_501 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_501 := by
  rule_auto rule_arithmetic_501

/-- `arithmetic.isle:507`. -/
theorem ok_rule_arithmetic_507 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_507 := by
  rule_auto rule_arithmetic_507

/-- `arithmetic.isle:513`. -/
theorem ok_rule_arithmetic_513 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_513 := by
  rule_auto rule_arithmetic_513

/-- `arithmetic.isle:520`. -/
theorem ok_rule_arithmetic_520 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_520 := by
  rule_auto rule_arithmetic_520

/-- `arithmetic.isle:526`. -/
theorem ok_rule_arithmetic_526 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_526 := by
  rule_auto rule_arithmetic_526

/-- `arithmetic.isle:532`. -/
theorem ok_rule_arithmetic_532 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_532 := by
  rule_auto rule_arithmetic_532

/-- `arithmetic.isle:539`. -/
theorem ok_rule_arithmetic_539 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_539 := by
  rule_auto rule_arithmetic_539

/-- `arithmetic.isle:546`. -/
theorem ok_rule_arithmetic_546 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_546 := by
  rule_auto rule_arithmetic_546

/-- `arithmetic.isle:552`. -/
theorem ok_rule_arithmetic_552 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_552 := by
  rule_auto rule_arithmetic_552

/-- `arithmetic.isle:558`. -/
theorem ok_rule_arithmetic_558 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_558 := by
  rule_auto rule_arithmetic_558

/-- `arithmetic.isle:564`. -/
theorem ok_rule_arithmetic_564 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_564 := by
  rule_auto rule_arithmetic_564

/-- `arithmetic.isle:571`. -/
theorem ok_rule_arithmetic_571 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_571 := by
  rule_auto rule_arithmetic_571

end Opt.Proof
