import FV.Opt.Proof.RuleAuto

/-!
# `opts/bitops.isle` (part 4): proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Roots `bitops.isle:537`..`664`; the roots of
this range that are not here are proven in `RuleBitops6.lean`/`RuleBitops7.lean` or listed as not proven in
`docs/contracts/midend.md` ("Rule proofs").
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:537`. -/
theorem ok_rule_bitops_537 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_537 := by
  rule_auto rule_bitops_537

/-- `bitops.isle:538`. -/
theorem ok_rule_bitops_538 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_538 := by
  rule_auto rule_bitops_538

/-- `bitops.isle:541`. -/
theorem ok_rule_bitops_541 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_541 := by
  rule_auto rule_bitops_541

/-- `bitops.isle:542`. -/
theorem ok_rule_bitops_542 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_542 := by
  rule_auto rule_bitops_542

/-- `bitops.isle:543`. -/
theorem ok_rule_bitops_543 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_543 := by
  rule_auto rule_bitops_543

/-- `bitops.isle:544`. -/
theorem ok_rule_bitops_544 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_544 := by
  rule_auto rule_bitops_544

/-- `bitops.isle:547`. -/
theorem ok_rule_bitops_547 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_547 := by
  rule_auto rule_bitops_547

/-- `bitops.isle:548`. -/
theorem ok_rule_bitops_548 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_548 := by
  rule_auto rule_bitops_548

/-- `bitops.isle:549`. -/
theorem ok_rule_bitops_549 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_549 := by
  rule_auto rule_bitops_549

/-- `bitops.isle:550`. -/
theorem ok_rule_bitops_550 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_550 := by
  rule_auto rule_bitops_550

/-- `bitops.isle:553`. -/
theorem ok_rule_bitops_553 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_553 := by
  rule_auto rule_bitops_553

/-- `bitops.isle:554`. -/
theorem ok_rule_bitops_554 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_554 := by
  rule_auto rule_bitops_554

/-- `bitops.isle:555`. -/
theorem ok_rule_bitops_555 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_555 := by
  rule_auto rule_bitops_555

/-- `bitops.isle:556`. -/
theorem ok_rule_bitops_556 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_556 := by
  rule_auto rule_bitops_556

/-- `bitops.isle:557`. -/
theorem ok_rule_bitops_557 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_557 := by
  rule_auto rule_bitops_557

/-- `bitops.isle:558`. -/
theorem ok_rule_bitops_558 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_558 := by
  rule_auto rule_bitops_558

/-- `bitops.isle:559`. -/
theorem ok_rule_bitops_559 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_559 := by
  rule_auto rule_bitops_559

/-- `bitops.isle:560`. -/
theorem ok_rule_bitops_560 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_560 := by
  rule_auto rule_bitops_560

/-- `bitops.isle:563`. -/
theorem ok_rule_bitops_563 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_563 := by
  rule_auto rule_bitops_563

/-- `bitops.isle:564`. -/
theorem ok_rule_bitops_564 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_564 := by
  rule_auto rule_bitops_564

/-- `bitops.isle:565`. -/
theorem ok_rule_bitops_565 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_565 := by
  rule_auto rule_bitops_565

/-- `bitops.isle:566`. -/
theorem ok_rule_bitops_566 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_566 := by
  rule_auto rule_bitops_566

/-- `bitops.isle:567`. -/
theorem ok_rule_bitops_567 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_567 := by
  rule_auto rule_bitops_567

/-- `bitops.isle:568`. -/
theorem ok_rule_bitops_568 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_568 := by
  rule_auto rule_bitops_568

/-- `bitops.isle:569`. -/
theorem ok_rule_bitops_569 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_569 := by
  rule_auto rule_bitops_569

/-- `bitops.isle:570`. -/
theorem ok_rule_bitops_570 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_570 := by
  rule_auto rule_bitops_570

/-- `bitops.isle:573`. -/
theorem ok_rule_bitops_573 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_573 := by
  rule_auto rule_bitops_573

/-- `bitops.isle:574`. -/
theorem ok_rule_bitops_574 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_574 := by
  rule_auto rule_bitops_574

/-- `bitops.isle:575`. -/
theorem ok_rule_bitops_575 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_575 := by
  rule_auto rule_bitops_575

/-- `bitops.isle:576`. -/
theorem ok_rule_bitops_576 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_576 := by
  rule_auto rule_bitops_576

/-- `bitops.isle:577`. -/
theorem ok_rule_bitops_577 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_577 := by
  rule_auto rule_bitops_577

/-- `bitops.isle:578`. -/
theorem ok_rule_bitops_578 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_578 := by
  rule_auto rule_bitops_578

/-- `bitops.isle:579`. -/
theorem ok_rule_bitops_579 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_579 := by
  rule_auto rule_bitops_579

/-- `bitops.isle:580`. -/
theorem ok_rule_bitops_580 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_580 := by
  rule_auto rule_bitops_580

/-- `bitops.isle:583`. -/
theorem ok_rule_bitops_583 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_583 := by
  rule_auto rule_bitops_583

/-- `bitops.isle:586`. -/
theorem ok_rule_bitops_586 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_586 := by
  rule_auto rule_bitops_586

/-- `bitops.isle:587`. -/
theorem ok_rule_bitops_587 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_587 := by
  rule_auto rule_bitops_587

/-- `bitops.isle:588`. -/
theorem ok_rule_bitops_588 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_588 := by
  rule_auto rule_bitops_588

/-- `bitops.isle:589`. -/
theorem ok_rule_bitops_589 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_589 := by
  rule_auto rule_bitops_589

/-- `bitops.isle:592`. -/
theorem ok_rule_bitops_592 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_592 := by
  rule_auto rule_bitops_592

/-- `bitops.isle:593`. -/
theorem ok_rule_bitops_593 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_593 := by
  rule_auto rule_bitops_593

/-- `bitops.isle:594`. -/
theorem ok_rule_bitops_594 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_594 := by
  rule_auto rule_bitops_594

/-- `bitops.isle:595`. -/
theorem ok_rule_bitops_595 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_595 := by
  rule_auto rule_bitops_595

/-- `bitops.isle:598`. -/
theorem ok_rule_bitops_598 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_598 := by
  rule_auto rule_bitops_598

/-- `bitops.isle:599`. -/
theorem ok_rule_bitops_599 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_599 := by
  rule_auto rule_bitops_599

/-- `bitops.isle:602`. -/
theorem ok_rule_bitops_602 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_602 := by
  rule_auto rule_bitops_602

/-- `bitops.isle:603`. -/
theorem ok_rule_bitops_603 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_603 := by
  rule_auto rule_bitops_603

/-- `bitops.isle:604`. -/
theorem ok_rule_bitops_604 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_604 := by
  rule_auto rule_bitops_604

/-- `bitops.isle:605`. -/
theorem ok_rule_bitops_605 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_605 := by
  rule_auto rule_bitops_605

/-- `bitops.isle:608`. -/
theorem ok_rule_bitops_608 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_608 := by
  rule_auto rule_bitops_608

/-- `bitops.isle:609`. -/
theorem ok_rule_bitops_609 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_609 := by
  rule_auto rule_bitops_609

/-- `bitops.isle:610`. -/
theorem ok_rule_bitops_610 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_610 := by
  rule_auto rule_bitops_610

/-- `bitops.isle:611`. -/
theorem ok_rule_bitops_611 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_611 := by
  rule_auto rule_bitops_611

/-- `bitops.isle:614`. -/
theorem ok_rule_bitops_614 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_614 := by
  rule_auto rule_bitops_614

/-- `bitops.isle:615`. -/
theorem ok_rule_bitops_615 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_615 := by
  rule_auto rule_bitops_615

/-- `bitops.isle:616`. -/
theorem ok_rule_bitops_616 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_616 := by
  rule_auto rule_bitops_616

/-- `bitops.isle:617`. -/
theorem ok_rule_bitops_617 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_617 := by
  rule_auto rule_bitops_617

/-- `bitops.isle:620`. -/
theorem ok_rule_bitops_620 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_620 := by
  rule_auto rule_bitops_620

/-- `bitops.isle:621`. -/
theorem ok_rule_bitops_621 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_621 := by
  rule_auto rule_bitops_621

/-- `bitops.isle:622`. -/
theorem ok_rule_bitops_622 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_622 := by
  rule_auto rule_bitops_622

/-- `bitops.isle:623`. -/
theorem ok_rule_bitops_623 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_623 := by
  rule_auto rule_bitops_623

/-- `bitops.isle:626`. -/
theorem ok_rule_bitops_626 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_626 := by
  rule_auto rule_bitops_626

/-- `bitops.isle:627`. -/
theorem ok_rule_bitops_627 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_627 := by
  rule_auto rule_bitops_627

/-- `bitops.isle:628`. -/
theorem ok_rule_bitops_628 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_628 := by
  rule_auto rule_bitops_628

/-- `bitops.isle:629`. -/
theorem ok_rule_bitops_629 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_629 := by
  rule_auto rule_bitops_629

/-- `bitops.isle:630`. -/
theorem ok_rule_bitops_630 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_630 := by
  rule_auto rule_bitops_630

/-- `bitops.isle:631`. -/
theorem ok_rule_bitops_631 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_631 := by
  rule_auto rule_bitops_631

/-- `bitops.isle:632`. -/
theorem ok_rule_bitops_632 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_632 := by
  rule_auto rule_bitops_632

/-- `bitops.isle:633`. -/
theorem ok_rule_bitops_633 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_633 := by
  rule_auto rule_bitops_633

/-- `bitops.isle:636`. -/
theorem ok_rule_bitops_636 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_636 := by
  rule_auto rule_bitops_636

/-- `bitops.isle:637`. -/
theorem ok_rule_bitops_637 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_637 := by
  rule_auto rule_bitops_637

/-- `bitops.isle:638`. -/
theorem ok_rule_bitops_638 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_638 := by
  rule_auto rule_bitops_638

/-- `bitops.isle:639`. -/
theorem ok_rule_bitops_639 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_639 := by
  rule_auto rule_bitops_639

/-- `bitops.isle:642`. -/
theorem ok_rule_bitops_642 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_642 := by
  rule_auto rule_bitops_642

/-- `bitops.isle:643`. -/
theorem ok_rule_bitops_643 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_643 := by
  rule_auto rule_bitops_643

/-- `bitops.isle:644`. -/
theorem ok_rule_bitops_644 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_644 := by
  rule_auto rule_bitops_644

/-- `bitops.isle:645`. -/
theorem ok_rule_bitops_645 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_645 := by
  rule_auto rule_bitops_645

/-- `bitops.isle:648`. -/
theorem ok_rule_bitops_648 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_648 := by
  rule_auto rule_bitops_648

/-- `bitops.isle:649`. -/
theorem ok_rule_bitops_649 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_649 := by
  rule_auto rule_bitops_649

/-- `bitops.isle:650`. -/
theorem ok_rule_bitops_650 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_650 := by
  rule_auto rule_bitops_650

/-- `bitops.isle:651`. -/
theorem ok_rule_bitops_651 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_651 := by
  rule_auto rule_bitops_651

/-- `bitops.isle:654`. -/
theorem ok_rule_bitops_654 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_654 := by
  rule_auto rule_bitops_654

/-- `bitops.isle:655`. -/
theorem ok_rule_bitops_655 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_655 := by
  rule_auto rule_bitops_655

/-- `bitops.isle:656`. -/
theorem ok_rule_bitops_656 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_656 := by
  rule_auto rule_bitops_656

/-- `bitops.isle:657`. -/
theorem ok_rule_bitops_657 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_657 := by
  rule_auto rule_bitops_657

/-- `bitops.isle:660`. -/
theorem ok_rule_bitops_660 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_660 := by
  rule_auto rule_bitops_660

/-- `bitops.isle:661`. -/
theorem ok_rule_bitops_661 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_661 := by
  rule_auto rule_bitops_661

/-- `bitops.isle:662`. -/
theorem ok_rule_bitops_662 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_662 := by
  rule_auto rule_bitops_662

/-- `bitops.isle:663`. -/
theorem ok_rule_bitops_663 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_663 := by
  rule_auto rule_bitops_663

/-- `bitops.isle:664`. -/
theorem ok_rule_bitops_664 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_664 := by
  rule_auto rule_bitops_664

end Opt.Proof
