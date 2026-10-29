module

public import FV.Opt.Proof.RuleAuto
public import FV.Opt.Proof.KernelBV

@[expose] public section

/-!
# Part 2 of 5 of `RuleArith.lean`

`FV/Opt/Proof/RuleArith.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `arithmetic.isle:13`. -/
theorem ok_rule_arithmetic_13 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_13 := by
  rule_auto rule_arithmetic_13

/-- `arithmetic.isle:31`. -/
theorem ok_rule_arithmetic_31 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_31 := by
  rule_auto rule_arithmetic_31

/-- `arithmetic.isle:240`. -/
theorem ok_rule_arithmetic_240 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_240 := by
  rule_auto rule_arithmetic_240

/-- `arithmetic.isle:296`. -/
theorem ok_rule_arithmetic_296 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_296 := by
  rule_auto rule_arithmetic_296

/-- `arithmetic.isle:303`. -/
theorem ok_rule_arithmetic_303 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_303 := by
  rule_auto rule_arithmetic_303

/-- `arithmetic.isle:312`. -/
theorem ok_rule_arithmetic_312 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_312 := by
  rule_auto rule_arithmetic_312

/-- `arithmetic.isle:319`. -/
theorem ok_rule_arithmetic_319 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_319 := by
  rule_auto rule_arithmetic_319

/-- `arithmetic.isle:338`. -/
theorem ok_rule_arithmetic_338 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_338 := by
  rule_auto rule_arithmetic_338

/-- `arithmetic.isle:353`. -/
theorem ok_rule_arithmetic_353 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_353 := by
  rule_auto rule_arithmetic_353

/-- `arithmetic.isle:358`. -/
theorem ok_rule_arithmetic_358 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_358 := by
  rule_auto rule_arithmetic_358

/-- `arithmetic.isle:365`. -/
theorem ok_rule_arithmetic_365 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_365 := by
  rule_auto rule_arithmetic_365

/-- `arithmetic.isle:372`. -/
theorem ok_rule_arithmetic_372 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_372 := by
  rule_auto rule_arithmetic_372

/-- `arithmetic.isle:379`. -/
theorem ok_rule_arithmetic_379 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_379 := by
  rule_auto rule_arithmetic_379

/-- `arithmetic.isle:388`. -/
theorem ok_rule_arithmetic_388 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_388 := by
  rule_auto rule_arithmetic_388

/-- `arithmetic.isle:451`. -/
theorem ok_rule_arithmetic_451 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_451 := by
  rule_auto rule_arithmetic_451

/-- `arithmetic.isle:458`. -/
theorem ok_rule_arithmetic_458 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_458 := by
  rule_auto rule_arithmetic_458

/-- `arithmetic.isle:463`. -/
theorem ok_rule_arithmetic_463 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_463 := by
  rule_auto rule_arithmetic_463

/-- `arithmetic.isle:470`. -/
theorem ok_rule_arithmetic_470 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_470 := by
  rule_auto rule_arithmetic_470

/-- `arithmetic.isle:477`. -/
theorem ok_rule_arithmetic_477 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_477 := by
  rule_auto rule_arithmetic_477

/-- `arithmetic.isle:482`. -/
theorem ok_rule_arithmetic_482 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_482 := by
  rule_auto rule_arithmetic_482

/-- `arithmetic.isle:487`. -/
theorem ok_rule_arithmetic_487 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_487 := by
  rule_auto rule_arithmetic_487

/-- `arithmetic.isle:492`. -/
theorem ok_rule_arithmetic_492 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_492 := by
  rule_auto rule_arithmetic_492

/-- `arithmetic.isle:500`. -/
theorem ok_rule_arithmetic_500 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_500 := by
  rule_auto rule_arithmetic_500

/-- `arithmetic.isle:506`. -/
theorem ok_rule_arithmetic_506 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_506 := by
  rule_auto rule_arithmetic_506

/-- `arithmetic.isle:512`. -/
theorem ok_rule_arithmetic_512 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_512 := by
  rule_auto rule_arithmetic_512

/-- `arithmetic.isle:518`. -/
theorem ok_rule_arithmetic_518 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_518 := by
  rule_auto rule_arithmetic_518

/-- `arithmetic.isle:525`. -/
theorem ok_rule_arithmetic_525 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_525 := by
  rule_auto rule_arithmetic_525

/-- `arithmetic.isle:531`. -/
theorem ok_rule_arithmetic_531 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_531 := by
  rule_auto rule_arithmetic_531

/-- `arithmetic.isle:538`. -/
theorem ok_rule_arithmetic_538 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_538 := by
  rule_auto rule_arithmetic_538

/-- `arithmetic.isle:544`. -/
theorem ok_rule_arithmetic_544 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_544 := by
  rule_auto rule_arithmetic_544

/-- `arithmetic.isle:551`. -/
theorem ok_rule_arithmetic_551 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_551 := by
  rule_auto rule_arithmetic_551

/-- `arithmetic.isle:557`. -/
theorem ok_rule_arithmetic_557 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_557 := by
  rule_auto rule_arithmetic_557

/-- `arithmetic.isle:563`. -/
theorem ok_rule_arithmetic_563 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_563 := by
  rule_auto rule_arithmetic_563

/-- `arithmetic.isle:569`. -/
theorem ok_rule_arithmetic_569 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_569 := by
  rule_auto rule_arithmetic_569

/-- `arithmetic.isle:599`. -/
theorem ok_rule_arithmetic_599 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_599 := by
  rule_auto rule_arithmetic_599

end Opt.Proof
