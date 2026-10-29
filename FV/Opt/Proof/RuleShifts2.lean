module

public import FV.Opt.Proof.RuleShifts2P1
public import FV.Opt.Proof.RuleShifts2P2
public import FV.Opt.Proof.RuleShifts2P3

@[expose] public section

/-!
# `opts/shifts.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleIntSplit.lean`, `RuleIntRetry.lean`); a `first` chain lists the
templates the rule was checked against, in order. Rules making `iconst_u`/`iconst_s` at a type
variable split it on `isInt` (`rule_auto_xzi`, `rule_auto_zi`): at a float type the constant
has no rule.
-/

-- The theorems live in `RuleShifts2P1` .. `RuleShifts2P3` (split to bound the elaboration memory).
