module

public import FV.Backend.Proof.KillBase
public import FV.Backend.Proof.IselContract

@[expose] public section

/-!
# Root and oracle policies for the certified ISLE term sets

Shared by the untrusted term-set generator and the kernel-checked certificates. The generator
proposes literal term sets; the consumers independently prove closure, root coverage and safety.
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-- The black-box oracle terms: the only builders of data with killed defs. -/
def killOracles : List TermId := [TId.atomic_rmw_loop, TId.atomic_cas_loop, TId.br_table_impl]

/-- The excluded root rules of `lower`: `nop` (587, hand-checked) and the I128 rules 636, 637
(never match). -/
def killExcl : List RuleId := [587, 636, 637]

/-- The terms the statement root rules apply. -/
def killRootsS : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => !killExcl.contains r.id).flatMap ruleTerms

/-- The terms the branch root rules apply. -/
def killRootsB : List TermId := (program.rulesOf TId.lower_branch).flatMap ruleTerms

end Backend.Proof.Kill

namespace E2E.LinkCheck

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-- The `call`/`call_indirect` rules of `lower`. -/
def callExcl : List RuleId := [1031, 1032, 1033]

/-- The terms the root rules apply: those of `lower` but 1031–1033, and those of the
closure-root rules of `lower_branch`. -/
def callRoots : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => !callExcl.contains r.id).flatMap ruleTerms ++
    ((program.rulesOf TId.lower_branch).filter fun r => closureRoot r).flatMap ruleTerms

/-- The terms the root rules apply: those of `lower` but the `return` rule (1037), and those of
`lower_branch`. -/
def retRoots : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => r.id != 1037).flatMap ruleTerms ++
    (program.rulesOf TId.lower_branch).flatMap ruleTerms

end E2E.LinkCheck
