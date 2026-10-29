module

public import FV.Opt.Proof.RuleRestEmbedBase
public import FV.Opt.Proof.RuleRestEmbedSshr
public import FV.Opt.Proof.RuleRestEmbedRotl
public import FV.Opt.Proof.RuleRestEmbedRotr

@[expose] public section

/-! # Templates for the remaining `simplify` roots (RulesRest)

The templates (`rule_auto_w`, `rule_auto_v`) and their helpers are in `RuleRestEmbedBase`;
the helper specifications `imm64_sshr`/`imm64_rotl`/`imm64_rotr` (simp set `opt_imm`)
are in `RuleRestEmbedSshr`/`Rotl`/`Rotr` (split to bound the elaboration memory). -/
