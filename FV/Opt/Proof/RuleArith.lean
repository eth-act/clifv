module

public import FV.Opt.Proof.RuleArithP1
public import FV.Opt.Proof.RuleArithP2
public import FV.Opt.Proof.RuleArithP3
public import FV.Opt.Proof.RuleArithP4
public import FV.Opt.Proof.RuleArithP5

@[expose] public section

/-!
# `opts/arithmetic.isle`: proven `simplify` rules

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`; the types `i8`..`i128` are all covered where the rule
applies. The 86 other `simplify` roots of the file are not proven yet (see `docs/contracts/midend.md`,
"Rule proofs": if-lets and internal constructors with if-lets (`iconst_u`/`iconst_s` on the right),
`imm64_power_of_two`, multiplication identities beyond the bit-level decision procedure, `iabs`;
lines 616-622 were left out because they hit a timeout under a full parallel build).
-/

-- The theorems live in `RuleArithP1` .. `RuleArithP5` (split to bound the elaboration memory).
