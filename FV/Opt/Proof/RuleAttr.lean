import Lean

/-!
# Simp sets for the mid-end rule proofs

* `opt_data`: generated facts about the exported mid-end program (`FV/Opt/Proof/RuleData.lean`:
  `termOf`, `rulesOf`, term kinds) — rule proofs are stated for an abstract `p` with `Data p`,
  so no proof unfolds `Isle.Opt.program`.
* `opt_match`: the relational reading of the matcher (`PatRel`, `ArgsRel`, `AllRel`), the
  embedding's extractors and `ofInst` inversion (`FV/Opt/Proof/RuleEmbed.lean`).
* `opt_monad`: monad laws for forward evaluation of right-hand sides (`FV/Opt/Proof/InterpEval.lean`).
* `opt_imm`: helper specifications, `Imm64` arithmetic as `BitVec` operations
  (`FV/Opt/Proof/RuleImm.lean`).
* `opt_lhs`: the rest of `lhs_step`'s set (`FV/Opt/Proof/RuleAuto.lean`), built once instead of
  from a list of names on every call.
-/

register_simp_attr opt_data
register_simp_attr opt_match
register_simp_attr opt_monad
register_simp_attr opt_imm
register_simp_attr opt_lhs
