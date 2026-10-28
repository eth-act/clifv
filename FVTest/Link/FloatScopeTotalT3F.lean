import FV.E2E.LinkScopeTotalTF
import FVTest.Link.FloatScopeInputT3F

/-! Non-vacuity of the decider-free float totality (S11f, #35, stage 2).

`%fs` (`FloatScopeInputT3F.lean`: float arithmetic, rounding, conversions, scalar `fcmp`; outside
`Compile.functionET`) meets every decided conjunct of `fnScopeInTB3F` (`scope3F_ok`, by
`native_decide`, witness only). By the theorems: the typed-try_call scope's run-time decider
holds (`lowersTCB_holds`), the function is in `fnScopeInTCB` (`tcb_holds`), and the cleanup
pipeline succeeds on it for every allocator answer (`pipeline_ok`).
`lake build FVTest.Link.FloatScopeTotalT3F`. -/

namespace E2E.FloatScopeTotalT3FWitness

open E2E E2E.LinkCheck Backend Backend.Proof Backend.Proof.Driver
open E2E.FloatScopeInputT3FWitness

theorem scope3F_ok : fnScopeInTB3F fS = true := by native_decide

/-- The run-time decider `lowersTCB` holds on `%fs` by `lowersTCB_of_T3F`. -/
theorem lowersTCB_holds : lowersTCB fS = true := lowersTCB_of_T3F scope3F_ok

/-- `%fs` is in `fnScopeInTCB` by `fnScopeInTCB_of_T3F`. -/
theorem tcb_holds : fnScopeInTCB fS = true := fnScopeInTCB_of_T3F scope3F_ok

/-- The cleanup pipeline succeeds on `%fs` by `pipeCleanupT_okT3F`, with the artifact passing
the float lowering validator. -/
theorem pipeline_ok (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeCleanupT fS k base o = .ok a ∧ lowerCheckTCF fS a.vc = true :=
  let ⟨a, ha, hc, -⟩ := pipeCleanupT_okT3F scope3F_ok k base o
  ⟨a, ha, hc⟩

end E2E.FloatScopeTotalT3FWitness
