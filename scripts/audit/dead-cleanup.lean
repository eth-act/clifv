import FV.E2E.DeadCleanupExecProven
import FV.E2E.DeadCleanupGuardedFP
import FV.E2E.UnwindValueSem
import FV.E2E.DeadCleanupOptProven
import FV.E2E.DeadCleanupFinal
import FV.Link.DeadCleanupExe
import FV.Link.DeadCleanupExeTotal
import FV.Backend.Proof.DeadCleanupCset
import FV.Backend.Proof.DeadCleanupPreparedAvailability

#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_proven
#print axioms E2E.backend_correct_opt_proven_cleanup
#print axioms E2E.backend_correct_final_cleanup
#print axioms Link.DeadCleanup.compileExe_correct
#print axioms Link.DeadCleanup.compileExe_total
#print axioms Backend.DeadCleanup.pureForm_of_pureNoFlags
#print axioms Backend.DeadCleanup.mspec_cmpOverwrite
#print axioms Backend.DeadCleanup.cmpOverwrite_of_mspec
#print axioms Backend.DeadCleanup.prune_correct
#print axioms Backend.DeadCleanup.valueSem_cmpOverwrite
#print axioms Backend.DeadCleanup.spec_mspec_csem
#print axioms Backend.Proof.valueSemV_cmpOverwrite
#print axioms Backend.DeadCleanup.valueSemU_cmpOverwrite
#print axioms Backend.Proof.valueSemVU_cmpOverwrite
#print axioms E2E.valueSemG_cmpOverwrite
#print axioms E2E.valueSemGF_cmpOverwrite
#print axioms Backend.DeadCleanup.scan_mono
#print axioms Backend.DeadCleanup.live_closed
#print axioms Backend.DeadCleanup.prepare_live_boundary
#print axioms Backend.DeadCleanup.preparedCleanup_spillAvail
#print axioms Backend.DeadCleanup.scanH_kept
#print axioms Backend.DeadCleanup.keptUses_eq_impl
#print axioms Backend.DeadCleanup.clean_eq_impl
#print axioms Backend.DeadCleanup.mspec_pure
#print axioms Backend.DeadCleanup.mspec_flagFree_pstate
