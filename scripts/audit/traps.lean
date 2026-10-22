import FV.E2E.DeadCleanupTrapCallWitness
import FV.E2E.WorldTrapCall
import FV.E2E.LinkTrapCallWitness

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
#print axioms E2E.regLevel_trapCall_world
#print axioms E2E.backend_correct_world_cleanup_trapcall
#print axioms E2E.DeadCleanupTrapCallWitness.final_applies -- witness: native_decide
#print axioms E2E.DeadCleanupTrapCallWitness.world_applies -- witness: native_decide
#print axioms E2E.DeadCleanupTrapCallWitness.cs0_trapsC
#print axioms E2E.DeadCleanupTrapCallWitness.cs0_not_trapsExplicit
#print axioms E2E.DeadCleanupTrapCallWitness.cs0_unwinds

-- S9c (#376): callee traps in the linked program (FV/E2E/LinkTrapCall*.lean).
#print axioms Backend.Proof.trap_udf_stop
#print axioms Backend.Proof.trap_trapIf_stop
#print axioms Backend.Proof.regLevel_trapStop_core
#print axioms E2E.regLevel_trapStop_world
#print axioms E2E.backend_correct_world_cleanup_trapstop
#print axioms E2E.postTrace_of_actGoodX
#print axioms E2E.step_restrictS
#print axioms E2E.step_congrE
#print axioms E2E.xCallsOk_cut
#print axioms E2E.xCallsIndOk_cut
#print axioms E2E.LinkSys.noRet_of_stop
#print axioms E2E.LinkSys.pcall_junk
#print axioms E2E.LinkSys.hooks_err
#print axioms E2E.LinkSys.progCallT
#print axioms E2E.LinkSys.progX_none
#print axioms E2E.LinkSys.xTrapsOk
#print axioms E2E.LinkSys.trapsExplicitC_cut
#print axioms E2E.LinkSys.runLoop_cut
#print axioms E2E.LinkSys.trapIn_callTrap
#print axioms E2E.LinkSys.thmT_of
#print axioms E2E.LinkSys.thmT
#print axioms E2E.LinkSys.trapIn_withCrun
#print axioms E2E.backend_correct_program_trap_core
#print axioms E2E.backend_correct_program_trap_budget
#print axioms E2E.backend_correct_program_trap
#print axioms E2E.backend_correct_program_trap_peak
#print axioms E2E.LinkTrapCallWitness.program_trap_applies -- witness: native_decide
#print axioms E2E.LinkTrapCallWitness.cs0_trapsD -- witness: native_decide
#print axioms E2E.LinkTrapCallWitness.cs0_not_trapsExplicit -- witness: native_decide
