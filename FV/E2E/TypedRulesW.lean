import FV.E2E.TypedRulesProg
import FV.Backend.Proof.IselLowerAllTI
import FV.Backend.Proof.IselMemAllTI
import FV.Backend.Proof.CtxTWTransport

/-!
# The typed rule families over `CtxTW` hold for the exported program (S11g, #1015)

The contexts of the typed scope with float `call`s (`Compile.functionETCF`) are `CtxTW`
(`CtxInvT` and the typed scope, without the integer-call facts `CallsE`/`CallArgsInt` of `CtxT`).
The families that never read those facts have `…W` forms over `CtxTW` (`LowerContractT`,
`LowerContractTP`), and `TypedRules` has `TypedRulesW`. Their proofs for `program` are the `CtxT`
proofs transported (`ctxW_transport`, `CtxTWTransport.lean`: the same proof terms with every `CtxT`
constant replaced, kernel-checked):

* `typedRulesW_program`, `lowerRulesCorrectTIW_program`, `memRulesCorrectRTIW_program`;
* `Driver.termCallsTW_of_rules`, `Driver.tryIndCallsTW_of_rules` (`termCallsT_of_rules`,
  `tryIndCallsT_of_rules` over `CtxTW`, from the `…W` families).

Each gives its `CtxT` form (`TypedRulesW.toT`, the families' `.toT`).
-/

namespace E2E

open Backend Backend.Proof

/-- **`TypedRules` over `CtxTW`**: the ten typed control families with the `CtxTW` forms of the
ones that never read the `call` facts (the `call` and `try_call` families stay over `CtxT`). -/
structure TypedRulesW : Prop where
  calls : CallRulesCorrectTP Isle.Aarch64.program
  ind : IndRulesCorrectTPW Isle.Aarch64.program
  term : LowerTermRulesCorrectTW Isle.Aarch64.program
  termUn : TermUnmatchableTW Isle.Aarch64.program
  branch : BranchRulesCorrectTW Isle.Aarch64.program
  branchEx : BranchExcludedUnmatchableTW Isle.Aarch64.program
  try_ : TryRulesCorrectTP Isle.Aarch64.program
  tryUn : TryUnmatchableT Isle.Aarch64.program
  tryInd : TryIndRulesCorrectTPW Isle.Aarch64.program
  tryIndUn : TryIndUnmatchableTW Isle.Aarch64.program

theorem TypedRulesW.toT (h : TypedRulesW) : TypedRules :=
  ⟨h.calls, h.ind.toT, h.term.toT, h.termUn.toT, h.branch.toT, h.branchEx.toT, h.try_, h.tryUn,
    h.tryInd.toT, h.tryIndUn.toT⟩

-- **The typed control families over `CtxTW` hold for the exported program.**
ctxW_transport typedRules_program => typedRulesW_program

-- `TypedRules.tryIndT` (the unpinned `try_call_indirect` family) over `CtxTW`.
ctxW_transport TypedRules.tryIndT => TypedRulesW.tryIndT

end E2E

namespace Backend.Proof

-- **The integer `lower` roots over `CtxTW`.**
ctxW_transport lowerRulesCorrectTI_program => lowerRulesCorrectTIW_program

-- **The integer memory roots over `CtxTW`.**
ctxW_transport memRulesCorrectRTI_program => memRulesCorrectRTIW_program

end Backend.Proof

namespace Backend.Proof.Driver

-- **`termCallsT_of_rules` over `CtxTW`.**
ctxW_transport termCallsT_of_rules => termCallsTW_of_rules

-- **`tryIndCallsT_of_rules` over `CtxTW`.**
ctxW_transport tryIndCallsT_of_rules => tryIndCallsTW_of_rules

end Backend.Proof.Driver
