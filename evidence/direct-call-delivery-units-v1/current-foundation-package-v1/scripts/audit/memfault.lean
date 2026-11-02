import FV.Clif.MemTrapWitness
import FV.E2E.MemTrapStatement
import FV.Backend.Proof.LowerSimMemTrap
import FV.Backend.Proof.PrepareMemTrap
import FV.E2E.RegLevelMemTrap
import FV.E2E.WorldMemTrap
import FV.E2E.LinkMemTrap
import FV.E2E.DeadCleanupExecMemTrap
import FV.Link.DeadCleanupExeMemTrap
import FV.Link.DeadCleanupExeMemTrapWitness
import FV.Front.RawExeMemTrap
import FV.E2E.DeadCleanupExecMemFault
import FV.Link.DeadCleanupExeMemFault
import FV.Link.DeadCleanupExeMemFaultWitness
import FV.Front.RawExeMemFault

-- A3 (#412): memory traps (docs/plans/memfault.md). F2/F3.
#print axioms Clif.memTrapAt_of_trapped
#print axioms E2E.TrapAtF.stepF
#print axioms Backend.Proof.atomicLowered_runTerm
#print axioms Backend.Proof.Driver.driver_memtrap
#print axioms Backend.Proof.Driver.memTraps_prep
#print axioms Clif.MemTrapWitness.f_memTrapAt -- witness: native_decide

-- F4: the register level and the per-function world theorem.
#print axioms E2E.instFaults_ldaxr
#print axioms Backend.Proof.realizes_haltLoop
#print axioms Backend.Proof.loop_ldaxr
#print axioms Backend.Proof.trapAtF_of_trapAtM
#print axioms Backend.Proof.regLevel_memtrap_world_value
#print axioms E2E.iselSim_relW_cleanup_memtrap
#print axioms E2E.backend_correct_worldX_cleanup_memtrap

-- F5: the linked program.
#print axioms E2E.LinkSys.runGoodB_of_trace
#print axioms E2E.backend_correct_program_memtrap_core
#print axioms E2E.backend_correct_program_memtrap_budget
#print axioms E2E.backend_correct_program_memtrap_peak

-- F6: the executable.
#print axioms E2E.DeadCleanupExecBytes.act_simNB
#print axioms E2E.DeadCleanupExecBytes.exec_of_trapAtM
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_memtrap
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_memtrap_peak
#print axioms Link.DeadCleanup.compileExe_correct_memtrap
#print axioms Link.DeadCleanup.compileExe_correct_memtrap_peak

-- F7: the source program and cg_clif's program.
#print axioms Link.DeadCleanup.compileExe_correct_source_memtrap
#print axioms Link.DeadCleanup.compileExe_correct_source_memtrap_peak
#print axioms Front.bundle_correct_source_memtrap
#print axioms Front.bundle_correct_source_memtrap_peak
#print axioms Front.bundle_correct_raw_memtrap
#print axioms Front.bundle_correct_raw_memtrap_peak
#print axioms Link.DeadCleanup.MemTrapWitness.exec_traps -- witness: native_decide
#print axioms Link.DeadCleanup.MemTrapWitness.cs0_mapFaults
#print axioms Link.DeadCleanup.MemTrapWitness.cs0_not_trapsExplicit

-- F8 (#443): no earlier access faults, every entry CLIF byte read-write (`MapRelRW`).
#print axioms Backend.Proof.realizes_allW
#print axioms Backend.Proof.RL.evsOk_of_goodXW
#print axioms E2E.ExecBytes.evsOk_congr
#print axioms E2E.backend_correct_worldX_cleanup_memtrapW
#print axioms E2E.backend_correct_world_niX_pipelineW
#print axioms E2E.LinkSys.thmGW
#print axioms E2E.backend_correct_program_memtrapW_budget
#print axioms E2E.backend_correct_program_memtrapW_peak
#print axioms E2E.DeadCleanupExecBytes.runX_stepF
#print axioms E2E.DeadCleanupExecBytes.act_simNF
#print axioms E2E.DeadCleanupExecBytes.act_simNBF
#print axioms E2E.DeadCleanupExecBytes.exec_of_trapAtMF
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_memtrapF_rw
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_memtrapF_rw_peak
#print axioms Link.DeadCleanup.compileExe_correct_memtrapF_rw
#print axioms Link.DeadCleanup.compileExe_correct_memtrapF_rw_peak
#print axioms Link.DeadCleanup.compileExe_correct_source_memtrapF_rw
#print axioms Link.DeadCleanup.compileExe_correct_source_memtrapF_rw_peak
#print axioms Front.bundle_correct_source_memtrapF_rw
#print axioms Front.bundle_correct_source_memtrapF_rw_peak
#print axioms Front.bundle_correct_raw_memtrapF_rw
#print axioms Front.bundle_correct_raw_memtrapF_rw_peak
#print axioms Link.DeadCleanup.MemTrapWitness.mapRelRW -- witness: native_decide
#print axioms Link.DeadCleanup.MemTrapWitness.exec_trapsF -- witness: native_decide
