import FV.E2E.DeadCleanupTrapCallWitness

-- S9 (#33): callee traps. S9a: the per-function theorem (docs/contracts/e2e.md "Callee traps").
#print axioms E2E.step_trapRel
#print axioms E2E.raiseAt_of_trapRel
#print axioms E2E.step_call_trap_stuck
#print axioms E2E.TrapsExplicit.toC
#print axioms E2E.reachX_trapEnv
#print axioms E2E.trapsExplicitX_trapEnv
#print axioms E2E.runLoopX_trapEnv
#print axioms E2E.trapEnv_of_trapped
#print axioms Backend.Proof.realizes_trapT
#print axioms Backend.Proof.regLevel_trapCall_core
#print axioms Backend.Proof.regLevel_trapCall_value
#print axioms E2E.xTrapsOk_of_noTrap
#print axioms E2E.xCallsOk_trapEnv
#print axioms E2E.xCallsIndOk_trapEnv
#print axioms E2E.xRaiseOk_trapEnv
#print axioms E2E.xRaiseIndOk_trapEnv
#print axioms E2E.backend_correct_final_cleanup_trapcall
#print axioms E2E.DeadCleanupTrapCallWitness.final_applies -- witness: native_decide
#print axioms E2E.DeadCleanupTrapCallWitness.cs0_trapsC
#print axioms E2E.DeadCleanupTrapCallWitness.cs0_not_trapsExplicit
#print axioms E2E.DeadCleanupTrapCallWitness.cs0_unwinds
