import FV.Link.DeadCleanupExeInitRC
import FV.Link.DeadCleanupExeInitSlotWitnessRU
import FV.Link.DeadCleanupExeInitTrapWitnessRC
import FV.Link.DeadCleanupExeInitTrapWitnessRU
import FV.E2E.BackendWorldPRBWitness
import FV.E2E.CallPostExistsWitness
import FV.E2E.LinkArmRetOkPRB

-- the oracle route (SEM1 #537, #713, #732, #733): the executable on decidable checks
#print axioms Link.DeadCleanup.compileExe_correct_initRC
#print axioms Link.DeadCleanup.compileExe_correct_initRCT
#print axioms Link.DeadCleanup.compileExe_correct_initRU
#print axioms Link.DeadCleanup.compileExe_correct_initTRU
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_initRC
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_initTRC
#print axioms E2E.DeadCleanupExecBytes.initOkRU_sysS_of_checks
#print axioms E2E.DeadCleanupExecBytes.baseNIX_closed
#print axioms E2E.DeadCleanupExecBytes.baseRetOk_closedSys
#print axioms E2E.DeadCleanupExecBytes.hooksKeep_closedSys
#print axioms E2E.hookNIX_closed
#print axioms E2E.LinkSys.initChecksB_sound
#print axioms E2E.LinkSys.needNI_of_slotsNIB
#print axioms E2E.DeadCleanupBinary.InitOkRU.of_checks
-- #733: RetCount / InvokedRetOk per parameter count
#print axioms E2E.LinkSys.agreeB_sound
#print axioms E2E.LinkSys.retCountB_sound
#print axioms E2E.LinkSys.retOkPRB_zero
#print axioms E2E.LinkSys.retOkPRB_of
#print axioms E2E.callPost_only_exists
#print axioms E2E.callPost_invoked_exists
#print axioms E2E.callPost_invokedN_exists
-- non-vacuity witnesses
#print axioms Link.DeadCleanup.InitSlotWitness.stale_read_returns_initRU -- witness: native_decide
#print axioms Link.DeadCleanup.InitTrapWitness.divz_traps_initRC -- witness: native_decide
#print axioms Link.DeadCleanup.InitTrapWitness.divz_traps_initRU -- witness: native_decide
#print axioms E2E.InvokedNWitness.invokedRetOk_sCall
#print axioms E2E.CallPostExistsWitness.callPost_e
