module

public import FV.Opt.Proof.RuleBitops2P1
public import FV.Opt.Proof.RuleBitops2P2
public import FV.Opt.Proof.RuleBitops2P3

@[expose] public section

/-!
# `opts/bitops.isle` (part 2): proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`. Roots `bitops.isle:294`..`420`; the roots of
this range that are not here are proven in `RuleBitops6.lean`/`RuleBitops7.lean` or listed as not proven in
`docs/contracts/midend.md` ("Rule proofs").
-/

-- The theorems live in `RuleBitops2P1` .. `RuleBitops2P3` (split to bound the elaboration memory).
