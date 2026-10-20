import FV.Opt.Proof.RuleAuto
import FV.Opt.Proof.KernelBV

/-!
# Part 1 of 5 of `RuleArith.lean`

`FV/Opt/Proof/RuleArith.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `arithmetic.isle:8`. -/
theorem ok_rule_arithmetic_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_8 := by
  rule_auto rule_arithmetic_8

/-- `arithmetic.isle:28`. -/
theorem ok_rule_arithmetic_28 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_28 := by
  rule_auto rule_arithmetic_28

/-- `arithmetic.isle:239`. -/
theorem ok_rule_arithmetic_239 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_239 := by
  rule_auto rule_arithmetic_239

/-- `arithmetic.isle:295`. -/
theorem ok_rule_arithmetic_295 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_295 := by
  rule_auto rule_arithmetic_295

/-- `arithmetic.isle:302`. -/
theorem ok_rule_arithmetic_302 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_302 := by
  rule_auto rule_arithmetic_302

/-- `arithmetic.isle:311`. -/
theorem ok_rule_arithmetic_311 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_311 := by
  rule_auto rule_arithmetic_311

/-- `arithmetic.isle:318`. -/
theorem ok_rule_arithmetic_318 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_318 := by
  rule_auto rule_arithmetic_318

/-- `arithmetic.isle:337`. -/
theorem ok_rule_arithmetic_337 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_337 := by
  rule_auto rule_arithmetic_337

/-- `arithmetic.isle:352`. -/
theorem ok_rule_arithmetic_352 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_352 := by
  rule_auto rule_arithmetic_352

/-- `arithmetic.isle:357`. -/
theorem ok_rule_arithmetic_357 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_357 := by
  rule_auto rule_arithmetic_357

/-- `arithmetic.isle:364`. -/
theorem ok_rule_arithmetic_364 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_364 := by
  rule_auto rule_arithmetic_364

/-- `arithmetic.isle:369`. -/
theorem ok_rule_arithmetic_369 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_369 := by
  rule_auto rule_arithmetic_369

/-- `arithmetic.isle:378`. -/
theorem ok_rule_arithmetic_378 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_378 := by
  rule_auto rule_arithmetic_378

/-- `arithmetic.isle:385`. -/
theorem ok_rule_arithmetic_385 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_385 := by
  rule_auto rule_arithmetic_385

/-- `arithmetic.isle:424`. -/
theorem ok_rule_arithmetic_424 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_424 := by
  rule_auto rule_arithmetic_424

/-- `arithmetic.isle:457`. -/
theorem ok_rule_arithmetic_457 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_457 := by
  rule_auto rule_arithmetic_457

/-- `arithmetic.isle:462`. -/
theorem ok_rule_arithmetic_462 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_462 := by
  rule_auto rule_arithmetic_462

/-- `arithmetic.isle:469`. -/
theorem ok_rule_arithmetic_469 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_469 := by
  rule_auto rule_arithmetic_469

/-- `arithmetic.isle:474`. -/
theorem ok_rule_arithmetic_474 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_474 := by
  rule_auto rule_arithmetic_474

/-- `arithmetic.isle:481`. -/
theorem ok_rule_arithmetic_481 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_481 := by
  rule_auto rule_arithmetic_481

/-- `arithmetic.isle:486`. -/
theorem ok_rule_arithmetic_486 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_486 := by
  rule_auto rule_arithmetic_486

/-- `arithmetic.isle:491`. -/
theorem ok_rule_arithmetic_491 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_491 := by
  rule_auto rule_arithmetic_491

/-- `arithmetic.isle:498`. -/
theorem ok_rule_arithmetic_498 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_498 := by
  rule_auto rule_arithmetic_498

/-- `arithmetic.isle:505`. -/
theorem ok_rule_arithmetic_505 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_505 := by
  rule_auto rule_arithmetic_505

/-- `arithmetic.isle:511`. -/
theorem ok_rule_arithmetic_511 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_511 := by
  rule_auto rule_arithmetic_511

/-- `arithmetic.isle:517`. -/
theorem ok_rule_arithmetic_517 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_517 := by
  rule_auto rule_arithmetic_517

/-- `arithmetic.isle:523`. -/
theorem ok_rule_arithmetic_523 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_523 := by
  rule_auto rule_arithmetic_523

/-- `arithmetic.isle:530`. -/
theorem ok_rule_arithmetic_530 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_530 := by
  rule_auto rule_arithmetic_530

/-- `arithmetic.isle:537`. -/
theorem ok_rule_arithmetic_537 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_537 := by
  rule_auto rule_arithmetic_537

/-- `arithmetic.isle:543`. -/
theorem ok_rule_arithmetic_543 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_543 := by
  rule_auto rule_arithmetic_543

/-- `arithmetic.isle:549`. -/
theorem ok_rule_arithmetic_549 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_549 := by
  rule_auto rule_arithmetic_549

/-- `arithmetic.isle:556`. -/
theorem ok_rule_arithmetic_556 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_556 := by
  rule_auto rule_arithmetic_556

/-- `arithmetic.isle:562`. -/
theorem ok_rule_arithmetic_562 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_562 := by
  rule_auto rule_arithmetic_562

/-- `arithmetic.isle:568`. -/
theorem ok_rule_arithmetic_568 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_568 := by
  rule_auto rule_arithmetic_568

/-- `arithmetic.isle:574`. -/
theorem ok_rule_arithmetic_574 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_574 := by
  rule_auto rule_arithmetic_574

end Opt.Proof
