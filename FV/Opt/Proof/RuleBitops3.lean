import FV.Opt.Proof.RuleAuto

/-!
# `opts/bitops.isle` (part 3): proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Roots `bitops.isle:421`..`536`; the roots of
this range that are not here are proven in `RuleBitops6.lean`/`RuleBitops7.lean` or listed as not proven in
`docs/contracts/midend.md` ("Rule proofs").
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:421`. -/
theorem ok_rule_bitops_421 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_421 := by
  rule_auto rule_bitops_421

/-- `bitops.isle:422`. -/
theorem ok_rule_bitops_422 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_422 := by
  rule_auto rule_bitops_422

/-- `bitops.isle:425`. -/
theorem ok_rule_bitops_425 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_425 := by
  rule_auto rule_bitops_425

/-- `bitops.isle:426`. -/
theorem ok_rule_bitops_426 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_426 := by
  rule_auto rule_bitops_426

/-- `bitops.isle:429`. -/
theorem ok_rule_bitops_429 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_429 := by
  rule_auto rule_bitops_429

/-- `bitops.isle:430`. -/
theorem ok_rule_bitops_430 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_430 := by
  rule_auto rule_bitops_430

/-- `bitops.isle:431`. -/
theorem ok_rule_bitops_431 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_431 := by
  rule_auto rule_bitops_431

/-- `bitops.isle:432`. -/
theorem ok_rule_bitops_432 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_432 := by
  rule_auto rule_bitops_432

/-- `bitops.isle:433`. -/
theorem ok_rule_bitops_433 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_433 := by
  rule_auto rule_bitops_433

/-- `bitops.isle:434`. -/
theorem ok_rule_bitops_434 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_434 := by
  rule_auto rule_bitops_434

/-- `bitops.isle:435`. -/
theorem ok_rule_bitops_435 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_435 := by
  rule_auto rule_bitops_435

/-- `bitops.isle:436`. -/
theorem ok_rule_bitops_436 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_436 := by
  rule_auto rule_bitops_436

/-- `bitops.isle:439`. -/
theorem ok_rule_bitops_439 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_439 := by
  rule_auto rule_bitops_439

/-- `bitops.isle:440`. -/
theorem ok_rule_bitops_440 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_440 := by
  rule_auto rule_bitops_440

/-- `bitops.isle:441`. -/
theorem ok_rule_bitops_441 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_441 := by
  rule_auto rule_bitops_441

/-- `bitops.isle:442`. -/
theorem ok_rule_bitops_442 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_442 := by
  rule_auto rule_bitops_442

/-- `bitops.isle:443`. -/
theorem ok_rule_bitops_443 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_443 := by
  rule_auto rule_bitops_443

/-- `bitops.isle:444`. -/
theorem ok_rule_bitops_444 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_444 := by
  rule_auto rule_bitops_444

/-- `bitops.isle:445`. -/
theorem ok_rule_bitops_445 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_445 := by
  rule_auto rule_bitops_445

/-- `bitops.isle:446`. -/
theorem ok_rule_bitops_446 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_446 := by
  rule_auto rule_bitops_446

/-- `bitops.isle:449`. -/
theorem ok_rule_bitops_449 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_449 := by
  rule_auto rule_bitops_449

/-- `bitops.isle:450`. -/
theorem ok_rule_bitops_450 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_450 := by
  rule_auto rule_bitops_450

/-- `bitops.isle:451`. -/
theorem ok_rule_bitops_451 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_451 := by
  rule_auto rule_bitops_451

/-- `bitops.isle:452`. -/
theorem ok_rule_bitops_452 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_452 := by
  rule_auto rule_bitops_452

/-- `bitops.isle:453`. -/
theorem ok_rule_bitops_453 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_453 := by
  rule_auto rule_bitops_453

/-- `bitops.isle:454`. -/
theorem ok_rule_bitops_454 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_454 := by
  rule_auto rule_bitops_454

/-- `bitops.isle:455`. -/
theorem ok_rule_bitops_455 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_455 := by
  rule_auto rule_bitops_455

/-- `bitops.isle:456`. -/
theorem ok_rule_bitops_456 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_456 := by
  rule_auto rule_bitops_456

/-- `bitops.isle:459`. -/
theorem ok_rule_bitops_459 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_459 := by
  rule_auto rule_bitops_459

/-- `bitops.isle:460`. -/
theorem ok_rule_bitops_460 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_460 := by
  rule_auto rule_bitops_460

/-- `bitops.isle:461`. -/
theorem ok_rule_bitops_461 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_461 := by
  rule_auto rule_bitops_461

/-- `bitops.isle:462`. -/
theorem ok_rule_bitops_462 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_462 := by
  rule_auto rule_bitops_462

/-- `bitops.isle:463`. -/
theorem ok_rule_bitops_463 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_463 := by
  rule_auto rule_bitops_463

/-- `bitops.isle:464`. -/
theorem ok_rule_bitops_464 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_464 := by
  rule_auto rule_bitops_464

/-- `bitops.isle:465`. -/
theorem ok_rule_bitops_465 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_465 := by
  rule_auto rule_bitops_465

/-- `bitops.isle:466`. -/
theorem ok_rule_bitops_466 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_466 := by
  rule_auto rule_bitops_466

/-- `bitops.isle:469`. -/
theorem ok_rule_bitops_469 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_469 := by
  rule_auto rule_bitops_469

/-- `bitops.isle:470`. -/
theorem ok_rule_bitops_470 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_470 := by
  rule_auto rule_bitops_470

/-- `bitops.isle:471`. -/
theorem ok_rule_bitops_471 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_471 := by
  rule_auto rule_bitops_471

/-- `bitops.isle:472`. -/
theorem ok_rule_bitops_472 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_472 := by
  rule_auto rule_bitops_472

/-- `bitops.isle:473`. -/
theorem ok_rule_bitops_473 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_473 := by
  rule_auto rule_bitops_473

/-- `bitops.isle:474`. -/
theorem ok_rule_bitops_474 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_474 := by
  rule_auto rule_bitops_474

/-- `bitops.isle:475`. -/
theorem ok_rule_bitops_475 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_475 := by
  rule_auto rule_bitops_475

/-- `bitops.isle:476`. -/
theorem ok_rule_bitops_476 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_476 := by
  rule_auto rule_bitops_476

/-- `bitops.isle:479`. -/
theorem ok_rule_bitops_479 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_479 := by
  rule_auto rule_bitops_479

/-- `bitops.isle:480`. -/
theorem ok_rule_bitops_480 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_480 := by
  rule_auto rule_bitops_480

/-- `bitops.isle:481`. -/
theorem ok_rule_bitops_481 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_481 := by
  rule_auto rule_bitops_481

/-- `bitops.isle:482`. -/
theorem ok_rule_bitops_482 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_482 := by
  rule_auto rule_bitops_482

/-- `bitops.isle:483`. -/
theorem ok_rule_bitops_483 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_483 := by
  rule_auto rule_bitops_483

/-- `bitops.isle:484`. -/
theorem ok_rule_bitops_484 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_484 := by
  rule_auto rule_bitops_484

/-- `bitops.isle:485`. -/
theorem ok_rule_bitops_485 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_485 := by
  rule_auto rule_bitops_485

/-- `bitops.isle:486`. -/
theorem ok_rule_bitops_486 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_486 := by
  rule_auto rule_bitops_486

/-- `bitops.isle:489`. -/
theorem ok_rule_bitops_489 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_489 := by
  rule_auto rule_bitops_489

/-- `bitops.isle:490`. -/
theorem ok_rule_bitops_490 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_490 := by
  rule_auto rule_bitops_490

/-- `bitops.isle:491`. -/
theorem ok_rule_bitops_491 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_491 := by
  rule_auto rule_bitops_491

/-- `bitops.isle:492`. -/
theorem ok_rule_bitops_492 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_492 := by
  rule_auto rule_bitops_492

/-- `bitops.isle:493`. -/
theorem ok_rule_bitops_493 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_493 := by
  rule_auto rule_bitops_493

/-- `bitops.isle:494`. -/
theorem ok_rule_bitops_494 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_494 := by
  rule_auto rule_bitops_494

/-- `bitops.isle:495`. -/
theorem ok_rule_bitops_495 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_495 := by
  rule_auto rule_bitops_495

/-- `bitops.isle:496`. -/
theorem ok_rule_bitops_496 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_496 := by
  rule_auto rule_bitops_496

/-- `bitops.isle:499`. -/
theorem ok_rule_bitops_499 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_499 := by
  rule_auto rule_bitops_499

/-- `bitops.isle:500`. -/
theorem ok_rule_bitops_500 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_500 := by
  rule_auto rule_bitops_500

/-- `bitops.isle:501`. -/
theorem ok_rule_bitops_501 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_501 := by
  rule_auto rule_bitops_501

/-- `bitops.isle:502`. -/
theorem ok_rule_bitops_502 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_502 := by
  rule_auto rule_bitops_502

/-- `bitops.isle:505`. -/
theorem ok_rule_bitops_505 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_505 := by
  rule_auto rule_bitops_505

/-- `bitops.isle:506`. -/
theorem ok_rule_bitops_506 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_506 := by
  rule_auto rule_bitops_506

/-- `bitops.isle:507`. -/
theorem ok_rule_bitops_507 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_507 := by
  rule_auto rule_bitops_507

/-- `bitops.isle:508`. -/
theorem ok_rule_bitops_508 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_508 := by
  rule_auto rule_bitops_508

/-- `bitops.isle:511`. -/
theorem ok_rule_bitops_511 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_511 := by
  rule_auto rule_bitops_511

/-- `bitops.isle:512`. -/
theorem ok_rule_bitops_512 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_512 := by
  rule_auto rule_bitops_512

/-- `bitops.isle:513`. -/
theorem ok_rule_bitops_513 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_513 := by
  rule_auto rule_bitops_513

/-- `bitops.isle:514`. -/
theorem ok_rule_bitops_514 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_514 := by
  rule_auto rule_bitops_514

/-- `bitops.isle:515`. -/
theorem ok_rule_bitops_515 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_515 := by
  rule_auto rule_bitops_515

/-- `bitops.isle:516`. -/
theorem ok_rule_bitops_516 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_516 := by
  rule_auto rule_bitops_516

/-- `bitops.isle:517`. -/
theorem ok_rule_bitops_517 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_517 := by
  rule_auto rule_bitops_517

/-- `bitops.isle:518`. -/
theorem ok_rule_bitops_518 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_518 := by
  rule_auto rule_bitops_518

/-- `bitops.isle:521`. -/
theorem ok_rule_bitops_521 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_521 := by
  rule_auto rule_bitops_521

/-- `bitops.isle:522`. -/
theorem ok_rule_bitops_522 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_522 := by
  rule_auto rule_bitops_522

/-- `bitops.isle:523`. -/
theorem ok_rule_bitops_523 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_523 := by
  rule_auto rule_bitops_523

/-- `bitops.isle:524`. -/
theorem ok_rule_bitops_524 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_524 := by
  rule_auto rule_bitops_524

/-- `bitops.isle:525`. -/
theorem ok_rule_bitops_525 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_525 := by
  rule_auto rule_bitops_525

/-- `bitops.isle:526`. -/
theorem ok_rule_bitops_526 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_526 := by
  rule_auto rule_bitops_526

/-- `bitops.isle:527`. -/
theorem ok_rule_bitops_527 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_527 := by
  rule_auto rule_bitops_527

/-- `bitops.isle:528`. -/
theorem ok_rule_bitops_528 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_528 := by
  rule_auto rule_bitops_528

/-- `bitops.isle:531`. -/
theorem ok_rule_bitops_531 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_531 := by
  rule_auto rule_bitops_531

/-- `bitops.isle:532`. -/
theorem ok_rule_bitops_532 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_532 := by
  rule_auto rule_bitops_532

/-- `bitops.isle:533`. -/
theorem ok_rule_bitops_533 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_533 := by
  rule_auto rule_bitops_533

/-- `bitops.isle:534`. -/
theorem ok_rule_bitops_534 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_534 := by
  rule_auto rule_bitops_534

/-- `bitops.isle:535`. -/
theorem ok_rule_bitops_535 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_535 := by
  rule_auto rule_bitops_535

/-- `bitops.isle:536`. -/
theorem ok_rule_bitops_536 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_536 := by
  rule_auto rule_bitops_536

end Opt.Proof
