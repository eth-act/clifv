import FV.E2E.TypedRulesS
import FV.Backend.Proof.LowerContractTPR
import FV.Backend.Proof.LowerContractTR
import FV.Backend.Proof.IselCtlCallTPR

/-!
# The typed indirect families with registers over an abstract scope (#753, stage R2)

`TypedRulesS` for the indirect families with registers: the `CtxT` proofs of #1188
(`indRulesCorrectTPR_program`, `tryIndRulesCorrectTPR_program`) and the typed
`try_call_indirect` dispatcher with registers (`Driver.tryIndCallsTR_of_rules`) transported to
`CtxTW` (`ctxWR_transport`) and to `CtxTS S` (`scopeSR_transport`), as `TypedRulesW` and
`TypedRulesS` transport the families without registers (the kernel checks every transported
declaration):

* `indRulesCorrectTPRW_program`, `tryIndRulesCorrectTPRW_program`,
  `indRulesCorrectTPRS_program`, `tryIndRulesCorrectTPRS_program`;
* `Driver.tryIndCallsTRW_of_rules`, `Driver.tryIndCallsTRS_of_rules`.
-/

namespace Backend.Proof

-- **The indirect families with registers over `CtxTW` hold for the exported program.**
ctxWR_transport indRulesCorrectTPR_program => indRulesCorrectTPRW_program
ctxWR_transport tryIndRulesCorrectTPR_program => tryIndRulesCorrectTPRW_program

-- **The indirect families with registers over `CtxTS S` hold for the exported program.**
scopeSR_transport indRulesCorrectTPRW_program => indRulesCorrectTPRS_program
scopeSR_transport tryIndRulesCorrectTPRW_program => tryIndRulesCorrectTPRS_program

end Backend.Proof

namespace Backend.Proof.Driver

-- **`tryIndCallsTR_of_rules` over `CtxTW` and over `CtxTS S`.**
ctxWR_transport tryIndCallsTR_of_rules => tryIndCallsTRW_of_rules
scopeSR_transport tryIndCallsTRW_of_rules => tryIndCallsTRS_of_rules

end Backend.Proof.Driver
