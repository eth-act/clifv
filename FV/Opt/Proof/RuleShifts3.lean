module

public import FV.Opt.Proof.RuleShifts3P1
public import FV.Opt.Proof.RuleShifts3P2

@[expose] public section

/-!
# `opts/shifts.isle` (part 3): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

-- The theorems live in `RuleShifts3P1` .. `RuleShifts3P2` (split to bound the elaboration memory).
