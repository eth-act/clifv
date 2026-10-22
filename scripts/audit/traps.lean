import FV.E2E.DeadCleanupTrapCallWitness
import FV.E2E.WorldTrapCall
import FV.E2E.LinkTrapCallWitness
import FV.Front.RawExeTrap
import FV.Link.DeadCleanupExeTrapWitness
import FV.E2E.DeadCleanupTrapCallTryWitness
import FV.Front.RawExeTrapT
import FV.Link.DeadCleanupExeTrapTWitness

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
-- S9d (#377): callee traps on the executable machine and in the bundle theorems
-- (FV/E2E/DeadCleanupExecTrap.lean, FV/Link/DeadCleanupExeTrap.lean, FV/Front/RawExeTrap.lean).
#print axioms E2E.LinkSys.progCallOk_bl
#print axioms E2E.LinkSys.progCallOk_blr
#print axioms E2E.DeadCleanupExecBytes.not_second_callPc
#print axioms E2E.DeadCleanupExecBytes.runOkSN_of_good
#print axioms E2E.DeadCleanupExecBytes.callsAt_of_progCallAt
#print axioms E2E.DeadCleanupExecBytes.stepOkD_progCall
#print axioms E2E.DeadCleanupExecBytes.exec_of_trapIn
#print axioms E2E.DeadCleanupExecBytes.exec_trap_of_model
#print axioms E2E.DeadCleanupExecBytes.trapsD_F
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_trap
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_trap_peak
#print axioms Link.DeadCleanup.lowerU_of
#print axioms Link.DeadCleanup.compileExe_correct_trap
#print axioms Link.DeadCleanup.compileExe_correct_trap_peak
#print axioms Link.DeadCleanup.compileExe_correct_source_trap
#print axioms Link.DeadCleanup.compileExe_correct_source_trap_peak
#print axioms Front.bundle_correct_source_trap
#print axioms Front.bundle_correct_source_trap_peak
#print axioms Front.bundle_correct_raw_trap
#print axioms Front.bundle_correct_raw_trap_peak
#print axioms Link.DeadCleanup.TrapWitness.exec_traps -- witness: native_decide
#print axioms Link.DeadCleanup.TrapWitness.cs0_trapsD -- witness: native_decide
#print axioms Link.DeadCleanup.TrapWitness.cs0_not_trapsExplicit -- witness: native_decide
-- S9b (#375), per function: callee traps of try_call/try_call_indirect
-- (FV/E2E/TrapCallTry*.lean, RegLevelTrapCallTry.lean, DeadCleanupTrapCallTry.lean).
#print axioms E2E.step_try_trap_stuck
#print axioms E2E.raiseAt_of_trapRel_try
#print axioms Backend.Proof.Driver.term_step_try_stop
#print axioms Backend.Proof.Driver.sim_trapStop
#print axioms Backend.Proof.Driver.driver_trapStop
#print axioms Backend.Proof.Driver.prep_sound_tryRaise
#print axioms E2E.tryRaise_cleanup
#print axioms Backend.Proof.star_haltTry
#print axioms Backend.Proof.realizes_haltTry
#print axioms Backend.Proof.regLevel_trapCall_coreT
#print axioms Backend.Proof.regLevel_trapCall_valueT
#print axioms E2E.backend_correct_final_cleanup_trapcallT
#print axioms E2E.DeadCleanupTrapCallTryWitness.final_applies -- witness: native_decide
#print axioms E2E.DeadCleanupTrapCallTryWitness.source_hasTry
#print axioms E2E.DeadCleanupTrapCallTryWitness.cs0_trapsCT
#print axioms E2E.DeadCleanupTrapCallTryWitness.cs0_traps
-- S9e (#408): try_call callee traps in the linked program, on the executable and in the bundles
-- (FV/E2E/WorldTrapStopT.lean, LinkTrapCallT.lean, DeadCleanupExecTrapT.lean,
-- FV/Link/DeadCleanupExeTrapT.lean, FV/Front/RawExeTrapT.lean).
#print axioms Backend.Proof.regLevel_trapStop_coreT
#print axioms E2E.regLevel_trapStop_worldT
#print axioms E2E.backend_correct_world_cleanup_trapstopT
#print axioms E2E.LinkSys.progCallTG
#print axioms E2E.LinkSys.xTrapsOkG
#print axioms E2E.LinkSys.trapIn_callTrapG
#print axioms E2E.LinkSys.thmTT
#print axioms E2E.backend_correct_program_trapT_budget
#print axioms E2E.backend_correct_program_trapT
#print axioms E2E.backend_correct_program_trapT_peak
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_trapT
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_trapT_peak
#print axioms Link.DeadCleanup.compileExe_correct_trapT
#print axioms Link.DeadCleanup.compileExe_correct_trapT_peak
#print axioms Link.DeadCleanup.compileExe_correct_source_trapT
#print axioms Link.DeadCleanup.compileExe_correct_source_trapT_peak
#print axioms Front.bundle_correct_source_trapT
#print axioms Front.bundle_correct_source_trapT_peak
#print axioms Front.bundle_correct_raw_trapT
#print axioms Front.bundle_correct_raw_trapT_peak
#print axioms Link.DeadCleanup.TrapTWitness.exec_traps -- witness: native_decide
#print axioms Link.DeadCleanup.TrapTWitness.cs0_trapsDT -- witness: native_decide
#print axioms Link.DeadCleanup.TrapTWitness.cs0_not_trapsD -- witness: native_decide
#print axioms Link.DeadCleanup.TrapTWitness.not_noTry -- witness: native_decide
