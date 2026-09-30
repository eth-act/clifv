import FV.Opt.Proof.RuleAuto

/-!
# `opts/bitops.isle` (part 5): proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Roots `bitops.isle:665`..`792`; the roots of
this range that are not here are proven in `RuleBitops6.lean`/`RuleBitops7.lean` or listed as not proven in
`docs/contracts/midend.md` ("Rule proofs").
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:665`. -/
theorem ok_rule_bitops_665 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_665 := by
  rule_auto rule_bitops_665

/-- `bitops.isle:666`. -/
theorem ok_rule_bitops_666 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_666 := by
  rule_auto rule_bitops_666

/-- `bitops.isle:667`. -/
theorem ok_rule_bitops_667 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_667 := by
  rule_auto rule_bitops_667

/-- `bitops.isle:670`. -/
theorem ok_rule_bitops_670 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_670 := by
  rule_auto rule_bitops_670

/-- `bitops.isle:671`. -/
theorem ok_rule_bitops_671 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_671 := by
  rule_auto rule_bitops_671

/-- `bitops.isle:672`. -/
theorem ok_rule_bitops_672 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_672 := by
  rule_auto rule_bitops_672

/-- `bitops.isle:673`. -/
theorem ok_rule_bitops_673 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_673 := by
  rule_auto rule_bitops_673

/-- `bitops.isle:674`. -/
theorem ok_rule_bitops_674 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_674 := by
  rule_auto rule_bitops_674

/-- `bitops.isle:675`. -/
theorem ok_rule_bitops_675 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_675 := by
  rule_auto rule_bitops_675

/-- `bitops.isle:676`. -/
theorem ok_rule_bitops_676 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_676 := by
  rule_auto rule_bitops_676

/-- `bitops.isle:677`. -/
theorem ok_rule_bitops_677 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_677 := by
  rule_auto rule_bitops_677

/-- `bitops.isle:678`. -/
theorem ok_rule_bitops_678 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_678 := by
  rule_auto rule_bitops_678

/-- `bitops.isle:679`. -/
theorem ok_rule_bitops_679 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_679 := by
  rule_auto rule_bitops_679

/-- `bitops.isle:680`. -/
theorem ok_rule_bitops_680 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_680 := by
  rule_auto rule_bitops_680

/-- `bitops.isle:681`. -/
theorem ok_rule_bitops_681 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_681 := by
  rule_auto rule_bitops_681

/-- `bitops.isle:682`. -/
theorem ok_rule_bitops_682 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_682 := by
  rule_auto rule_bitops_682

/-- `bitops.isle:683`. -/
theorem ok_rule_bitops_683 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_683 := by
  rule_auto rule_bitops_683

/-- `bitops.isle:684`. -/
theorem ok_rule_bitops_684 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_684 := by
  rule_auto rule_bitops_684

/-- `bitops.isle:685`. -/
theorem ok_rule_bitops_685 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_685 := by
  rule_auto rule_bitops_685

/-- `bitops.isle:688`. -/
theorem ok_rule_bitops_688 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_688 := by
  rule_auto rule_bitops_688

/-- `bitops.isle:689`. -/
theorem ok_rule_bitops_689 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_689 := by
  rule_auto rule_bitops_689

/-- `bitops.isle:690`. -/
theorem ok_rule_bitops_690 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_690 := by
  rule_auto rule_bitops_690

/-- `bitops.isle:691`. -/
theorem ok_rule_bitops_691 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_691 := by
  rule_auto rule_bitops_691

/-- `bitops.isle:694`. -/
theorem ok_rule_bitops_694 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_694 := by
  rule_auto rule_bitops_694

/-- `bitops.isle:697`. -/
theorem ok_rule_bitops_697 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_697 := by
  rule_auto rule_bitops_697

/-- `bitops.isle:698`. -/
theorem ok_rule_bitops_698 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_698 := by
  rule_auto rule_bitops_698

/-- `bitops.isle:699`. -/
theorem ok_rule_bitops_699 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_699 := by
  rule_auto rule_bitops_699

/-- `bitops.isle:700`. -/
theorem ok_rule_bitops_700 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_700 := by
  rule_auto rule_bitops_700

/-- `bitops.isle:701`. -/
theorem ok_rule_bitops_701 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_701 := by
  rule_auto rule_bitops_701

/-- `bitops.isle:702`. -/
theorem ok_rule_bitops_702 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_702 := by
  rule_auto rule_bitops_702

/-- `bitops.isle:703`. -/
theorem ok_rule_bitops_703 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_703 := by
  rule_auto rule_bitops_703

/-- `bitops.isle:704`. -/
theorem ok_rule_bitops_704 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_704 := by
  rule_auto rule_bitops_704

/-- `bitops.isle:707`. -/
theorem ok_rule_bitops_707 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_707 := by
  rule_auto rule_bitops_707

/-- `bitops.isle:708`. -/
theorem ok_rule_bitops_708 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_708 := by
  rule_auto rule_bitops_708

/-- `bitops.isle:709`. -/
theorem ok_rule_bitops_709 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_709 := by
  rule_auto rule_bitops_709

/-- `bitops.isle:710`. -/
theorem ok_rule_bitops_710 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_710 := by
  rule_auto rule_bitops_710

/-- `bitops.isle:711`. -/
theorem ok_rule_bitops_711 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_711 := by
  rule_auto rule_bitops_711

/-- `bitops.isle:712`. -/
theorem ok_rule_bitops_712 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_712 := by
  rule_auto rule_bitops_712

/-- `bitops.isle:713`. -/
theorem ok_rule_bitops_713 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_713 := by
  rule_auto rule_bitops_713

/-- `bitops.isle:714`. -/
theorem ok_rule_bitops_714 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_714 := by
  rule_auto rule_bitops_714

/-- `bitops.isle:717`. -/
theorem ok_rule_bitops_717 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_717 := by
  rule_auto rule_bitops_717

/-- `bitops.isle:718`. -/
theorem ok_rule_bitops_718 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_718 := by
  rule_auto rule_bitops_718

/-- `bitops.isle:719`. -/
theorem ok_rule_bitops_719 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_719 := by
  rule_auto rule_bitops_719

/-- `bitops.isle:720`. -/
theorem ok_rule_bitops_720 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_720 := by
  rule_auto rule_bitops_720

/-- `bitops.isle:721`. -/
theorem ok_rule_bitops_721 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_721 := by
  rule_auto rule_bitops_721

/-- `bitops.isle:722`. -/
theorem ok_rule_bitops_722 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_722 := by
  rule_auto rule_bitops_722

/-- `bitops.isle:723`. -/
theorem ok_rule_bitops_723 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_723 := by
  rule_auto rule_bitops_723

/-- `bitops.isle:724`. -/
theorem ok_rule_bitops_724 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_724 := by
  rule_auto rule_bitops_724

/-- `bitops.isle:727`. -/
theorem ok_rule_bitops_727 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_727 := by
  rule_auto rule_bitops_727

/-- `bitops.isle:728`. -/
theorem ok_rule_bitops_728 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_728 := by
  rule_auto rule_bitops_728

/-- `bitops.isle:729`. -/
theorem ok_rule_bitops_729 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_729 := by
  rule_auto rule_bitops_729

/-- `bitops.isle:730`. -/
theorem ok_rule_bitops_730 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_730 := by
  rule_auto rule_bitops_730

/-- `bitops.isle:731`. -/
theorem ok_rule_bitops_731 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_731 := by
  rule_auto rule_bitops_731

/-- `bitops.isle:732`. -/
theorem ok_rule_bitops_732 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_732 := by
  rule_auto rule_bitops_732

/-- `bitops.isle:733`. -/
theorem ok_rule_bitops_733 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_733 := by
  rule_auto rule_bitops_733

/-- `bitops.isle:734`. -/
theorem ok_rule_bitops_734 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_734 := by
  rule_auto rule_bitops_734

/-- `bitops.isle:783`. -/
theorem ok_rule_bitops_783 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_783 := by
  rule_auto rule_bitops_783

/-- `bitops.isle:784`. -/
theorem ok_rule_bitops_784 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_784 := by
  rule_auto rule_bitops_784

/-- `bitops.isle:785`. -/
theorem ok_rule_bitops_785 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_785 := by
  rule_auto rule_bitops_785

/-- `bitops.isle:786`. -/
theorem ok_rule_bitops_786 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_786 := by
  rule_auto rule_bitops_786

end Opt.Proof
