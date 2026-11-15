import FV.E2E.TypedRulesW
import FV.Backend.Proof.LowerContractTS

/-!
# The typed rule families over an abstract scope hold for the exported program (#1002 part 2)

`TypedRulesW` (S11g) over `CtxTS S` for every scope `S : InstScope` (`TypedRulesS S`). Their
proofs for `program` are the `CtxTW` proofs transported (`scopeS_transport`,
`ScopeTransport.lean`: the same proof terms with every `CtxTW` constant replaced by its
scope-generic counterpart, abstracted over `S`, kernel-checked):

* `typedRulesS_program`, `TypedRulesS.tryIndT`, `lowerRulesCorrectTIS_program`,
  `memRulesCorrectRTIS_program`;
* `Driver.termCallsTS_of_rules`, `Driver.tryIndCallsTS_of_rules`.

`TypedRulesW` and its theorems are unchanged.
-/

namespace E2E

open Backend Backend.Proof

/-- **`TypedRulesW` over `CtxTS S`**: the ten typed control families with the scope-generic forms
of the ones over `CtxTW`. -/
structure TypedRulesS (S : InstScope) : Prop where
  calls : CallRulesCorrectTP Isle.Aarch64.program
  ind : IndRulesCorrectTPS S Isle.Aarch64.program
  term : LowerTermRulesCorrectTS S Isle.Aarch64.program
  termUn : TermUnmatchableTS S Isle.Aarch64.program
  branch : BranchRulesCorrectTS S Isle.Aarch64.program
  branchEx : BranchExcludedUnmatchableTS S Isle.Aarch64.program
  try_ : TryRulesCorrectTP Isle.Aarch64.program
  tryUn : TryUnmatchableT Isle.Aarch64.program
  tryInd : TryIndRulesCorrectTPS S Isle.Aarch64.program
  tryIndUn : TryIndUnmatchableTS S Isle.Aarch64.program

-- **The typed control families over `CtxTS S` hold for the exported program.**
scopeS_transport typedRulesW_program => typedRulesS_program

-- `TypedRulesW.tryIndT` over `CtxTS S`.
scopeS_transport TypedRulesW.tryIndT => TypedRulesS.tryIndT

end E2E

namespace Backend.Proof

-- **The integer `lower` roots over `CtxTS S`.**
scopeS_transport lowerRulesCorrectTIW_program => lowerRulesCorrectTIS_program

-- **The integer memory roots over `CtxTS S`.**
scopeS_transport memRulesCorrectRTIW_program => memRulesCorrectRTIS_program

end Backend.Proof

namespace Backend.Proof.Driver

-- **`termCallsTW_of_rules` over `CtxTS S`.**
scopeS_transport termCallsTW_of_rules => termCallsTS_of_rules

-- **`tryIndCallsTW_of_rules` over `CtxTS S`.**
scopeS_transport tryIndCallsTW_of_rules => tryIndCallsTS_of_rules

end Backend.Proof.Driver
