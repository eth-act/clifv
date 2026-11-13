import FV.Backend.Proof.KillBase
import FV.Backend.Proof.IselContract

/-!
# Root policy of the pool-free ISLE term set (#1002)

Shared by the untrusted term-set generator (`FVTest/Backend/TermSetGen.lean --pool`) and the
kernel-checked certificate (`IselPoolFree`): the terms `poolTab` is closed from. The lowering
reaches the literal pool (`emit_u64_le_const`, #565) through `constant_f64`'s last rule only, and
`constant_f64` through the `f64const` rule of `lower` (and vector rules outside the closure); so
the roots leave out that rule and `constant_f64` itself, and keep what its other rules apply.
-/

namespace Backend.Proof.Pool

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-- The root rule of `lower` the set excludes: `f64const`'s (`lower.isle:68`, id 585,
hand-checked on a constant without literal pool). -/
def poolExcl : List RuleId := [585]

/-- `constant_f64`'s literal-pool rule (`inst.isle:4275`, id 401). -/
def poolRule : RuleId := 401

/-- The terms the root rules apply: those of the closure-root rules of `lower` but 585, those of
`lower_branch`, and those of `constant_f64`'s rules without literal pool with `output_reg` (the
right-hand side of rule 585 on a constant without literal pool). -/
def poolRoots : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => closureRoot r && !poolExcl.contains r.id).flatMap
      ruleTerms ++
    (program.rulesOf TId.lower_branch).flatMap ruleTerms ++
    ((program.rulesOf TId.constant_f64).filter fun r => r.id != poolRule).flatMap ruleTerms ++
    [TId.output_reg]

end Backend.Proof.Pool
