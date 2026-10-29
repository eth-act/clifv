module

public import FV.Opt.Proof.RuleAuto
public import FV.Opt.Proof.KernelBV

@[expose] public section

/-!
# Part 4 of 5 of `RuleArith.lean`

`FV/Opt/Proof/RuleArith.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `arithmetic.isle:24`. -/
theorem ok_rule_arithmetic_24 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_24 := by
  rule_auto rule_arithmetic_24

/-- `arithmetic.isle:59`. -/
theorem ok_rule_arithmetic_59 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_59 := by
  rule_auto rule_arithmetic_59

/-- `arithmetic.isle:244`. -/
theorem ok_rule_arithmetic_244 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_244 := by
  rule_auto rule_arithmetic_244

/-- `arithmetic.isle:298`. -/
theorem ok_rule_arithmetic_298 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_298 := by
  rule_auto rule_arithmetic_298

/-- `arithmetic.isle:307`. -/
theorem ok_rule_arithmetic_307 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_307 := by
  rule_auto rule_arithmetic_307

/-- `arithmetic.isle:314`. -/
theorem ok_rule_arithmetic_314 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_314 := by
  rule_auto rule_arithmetic_314

/-- `arithmetic.isle:323`. -/
theorem ok_rule_arithmetic_323 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_323 := by
  rule_auto rule_arithmetic_323

/-- `arithmetic.isle:340`. -/
theorem ok_rule_arithmetic_340 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_340 := by
  rule_auto rule_arithmetic_340

/-- `arithmetic.isle:355`. -/
theorem ok_rule_arithmetic_355 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_355 := by
  rule_auto rule_arithmetic_355

/-- `arithmetic.isle:362`. -/
theorem ok_rule_arithmetic_362 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_362 := by
  rule_auto rule_arithmetic_362

/-- `arithmetic.isle:367`. -/
theorem ok_rule_arithmetic_367 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_367 := by
  rule_auto rule_arithmetic_367

/-- `arithmetic.isle:374`. -/
theorem ok_rule_arithmetic_374 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_374 := by
  rule_auto rule_arithmetic_374

/-- `arithmetic.isle:381`. -/
theorem ok_rule_arithmetic_381 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_381 := by
  rule_auto rule_arithmetic_381

/-- `arithmetic.isle:390`. -/
theorem ok_rule_arithmetic_390 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_390 := by
  rule_auto rule_arithmetic_390

/-- `arithmetic.isle:453`. -/
theorem ok_rule_arithmetic_453 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_453 := by
  rule_auto rule_arithmetic_453

/-- `arithmetic.isle:460`. -/
theorem ok_rule_arithmetic_460 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_460 := by
  rule_auto rule_arithmetic_460

/-- `arithmetic.isle:467`. -/
theorem ok_rule_arithmetic_467 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_467 := by
  rule_auto rule_arithmetic_467

/-- `arithmetic.isle:472`. -/
theorem ok_rule_arithmetic_472 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_472 := by
  rule_auto rule_arithmetic_472

/-- `arithmetic.isle:479`. -/
theorem ok_rule_arithmetic_479 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_479 := by
  rule_auto rule_arithmetic_479

/-- `arithmetic.isle:484`. -/
theorem ok_rule_arithmetic_484 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_484 := by
  rule_auto rule_arithmetic_484

/-- `arithmetic.isle:489`. -/
theorem ok_rule_arithmetic_489 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_489 := by
  rule_auto rule_arithmetic_489

/-- `arithmetic.isle:496`. -/
theorem ok_rule_arithmetic_496 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_496 := by
  rule_auto rule_arithmetic_496

/-- `arithmetic.isle:502`. -/
theorem ok_rule_arithmetic_502 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_502 := by
  rule_auto rule_arithmetic_502

/-- `arithmetic.isle:508`. -/
theorem ok_rule_arithmetic_508 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_508 := by
  rule_auto rule_arithmetic_508

/-- `arithmetic.isle:515`. -/
theorem ok_rule_arithmetic_515 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_515 := by
  rule_auto rule_arithmetic_515

/-- `arithmetic.isle:521`. -/
theorem ok_rule_arithmetic_521 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_521 := by
  rule_auto rule_arithmetic_521

/-- `arithmetic.isle:527`. -/
theorem ok_rule_arithmetic_527 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_527 := by
  rule_auto rule_arithmetic_527

/-- `arithmetic.isle:533`. -/
theorem ok_rule_arithmetic_533 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_533 := by
  rule_auto rule_arithmetic_533

/-- `arithmetic.isle:541`. -/
theorem ok_rule_arithmetic_541 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_541 := by
  rule_auto rule_arithmetic_541

/-- `arithmetic.isle:547`. -/
theorem ok_rule_arithmetic_547 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_547 := by
  rule_auto rule_arithmetic_547

/-- `arithmetic.isle:553`. -/
theorem ok_rule_arithmetic_553 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_553 := by
  rule_auto rule_arithmetic_553

/-- `arithmetic.isle:559`. -/
theorem ok_rule_arithmetic_559 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_559 := by
  rule_auto rule_arithmetic_559

/-- `arithmetic.isle:566`. -/
theorem ok_rule_arithmetic_566 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_566 := by
  rule_auto rule_arithmetic_566

/-- `arithmetic.isle:572`. -/
theorem ok_rule_arithmetic_572 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_572 := by
  rule_auto rule_arithmetic_572

end Opt.Proof
