import FV.Front.RawExeNB
import FV.Front.RawExeBaselineNB
import FV.Front.RawExeTrapNB
import FV.Link.DeadCleanupExeTrapNBWitness
import FV.Link.DeadCleanupExeTrapPeakNBWitness
#print axioms E2E.SrcBounded.step_next_rich
#print axioms E2E.SrcBounded.bounded_slotless
#print axioms E2E.SrcBounded.bounded_placed
#print axioms E2E.SrcBounded.indSig_legal
#print axioms E2E.SrcBounded.callee_of_enter
#print axioms Link.DeadCleanup.srcBounded_gen
#print axioms Link.DeadCleanup.srcBounded_acyclic
#print axioms Link.DeadCleanup.srcBounded_peak
#print axioms Link.DeadCleanup.compileExe_correct_source_nobnd
#print axioms Link.DeadCleanup.compileExe_correct_source_peak_nobnd
#print axioms Front.bundle_correct_source_nobnd
#print axioms Front.bundle_correct_source_peak_nobnd
#print axioms Front.bundle_correct_raw_nobnd
#print axioms Front.bundle_correct_raw_peak_nobnd
#print axioms Link.DeadCleanup.ident_entry
#print axioms Link.DeadCleanup.compileExe_correct_source_trap_nobnd
#print axioms Link.DeadCleanup.compileExe_correct_source_trap_peak_nobnd
#print axioms Front.bundle_correct_source_trap_nobnd
#print axioms Front.bundle_correct_source_trap_peak_nobnd
#print axioms Front.bundle_correct_raw_trap_nobnd
#print axioms Front.bundle_correct_raw_trap_peak_nobnd
#print axioms Link.DeadCleanup.TrapWitness.exec_source_traps -- witness: native_decide
#print axioms Link.DeadCleanup.TrapWitness.cs0_trapsD_all -- witness: native_decide
#print axioms Link.DeadCleanup.TrapWitness.src_noMemTrap -- witness: native_decide
#print axioms Link.DeadCleanup.TrapWitness.peak_trapsD_all
#print axioms Link.DeadCleanup.TrapWitness.exec_source_traps_peak -- witness: native_decide
#print axioms Link.srcBounded_gen
#print axioms Link.srcBounded_acyclic
#print axioms Link.srcBounded_peak
#print axioms Link.compileExe_correct_source_nobnd
#print axioms Link.compileExe_correct_source_peak_nobnd
#print axioms Front.bundle_correct_source_baseline_nobnd
#print axioms Front.bundle_correct_source_peak_baseline_nobnd
#print axioms Front.bundle_correct_raw_baseline_nobnd
#print axioms Front.bundle_correct_raw_peak_baseline_nobnd
