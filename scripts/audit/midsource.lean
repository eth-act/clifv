import FV.Link.MidSource
import FV.Link.MidPair
import FV.Link.MidProg
import FV.Link.MidSourceRoutes
import FV.E2E.MidValExecProven
import FVTest.Link.MidPairWitness
import FVTest.Link.MidSourceWitness
import FV.Link.MidSourceTB
import FVTest.Link.MidSourceTBWitness
import FV.Opt.Proof.MidValSymsSim
import FV.Link.MidPairSyms
import FV.Link.MidProgSyms
import FV.Link.MidSourceRoutesSyms
import FV.Link.MidSourceTBSyms
import FV.E2E.MidValExecProvenSyms
import FVTest.Link.MidSymsWitness
import FVTest.Link.MidSourceSymsWitness

/-! #1119 layer 2: the bundle's program through the mid-end validator (and its hoisting mode at the executable's symbol table). -/

#print axioms Opt.Stut.reachesX_split
#print axioms Opt.runLoopX_refinesSRMU_depth
#print axioms Opt.stepX_toX_of_next
#print axioms Opt.reachesX_toX_of_reaches
#print axioms Opt.reaches_of_reachesX_toX
#print axioms Link.midEntry_srMU
#print axioms Link.validated_find
#print axioms Link.midSource
#print axioms Link.midSource_depth
#print axioms Link.midPairB_sound
#print axioms Link.midValidatedB_sound
#print axioms Link.midProg_sim
#print axioms Link.midProg
#print axioms Link.midProg_depth
#print axioms E2E.ReturnPinExecBytes.binary_correct_exec_proven_mid
#print axioms E2E.ReturnPinExecBytes.binary_correct_exec_peak_proven_mid
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTS_mid
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS_mid
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_provenT_mid
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT_mid
#print axioms Link.compileExe_correct_sourceMid
#print axioms Link.compileExe_correct_source_peakMid
#print axioms Link.DeadCleanup.compileExe_correct_sourceMid
#print axioms Link.DeadCleanup.compileExe_correct_source_peakMid
#print axioms Link.compileExeOpt_correct_sourceMid
#print axioms Link.compileExeOpt_correct_source_peakMid
#print axioms Link.DeadCleanup.compileExeOpt_correct_sourceMid
#print axioms Link.DeadCleanup.compileExeOpt_correct_source_peakMid
#print axioms Link.DeadCleanup.compileExeT_correct_sourceMid
#print axioms Link.DeadCleanup.compileExeT_correct_source_peakMid
#print axioms Link.ReturnPinCompilerWith.attempt_correct_sourceMid
#print axioms Link.ReturnPinCompilerWith.attempt_correct_source_peakMid
#print axioms Link.SemanticCompilerWith.attempt_correct_sourceMid
#print axioms Link.SemanticCompilerWith.attempt_correct_source_peakMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakMid
#print axioms Link.TypedCompilerWith.attempt_correct_sourceMid
#print axioms Link.TypedCompilerWith.attempt_correct_source_peakMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceTBMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakTBMid
#print axioms FVTest.Link.MidPairWitness.facts0 -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.facts_spec -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.validated -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.midProg_applies -- witness: native_decide
#print axioms Link.MidSourceWitness.checks_true -- witness: native_decide
#print axioms Link.MidSourceWitness.parts -- witness: native_decide
#print axioms Link.MidSourceWitness.correct_sourceMid_applies -- witness: native_decide
#print axioms Link.MidSourceWitness.hcp
#print axioms E2E.MidSourceTBWitness.checks_true -- witness: native_decide
#print axioms E2E.MidSourceTBWitness.parts -- witness: native_decide
#print axioms E2E.MidSourceTBWitness.correct_sourceTBMid_applies -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.keep_empty
#print axioms Opt.runLoopX_refinesSRMUAt_depth
#print axioms Opt.MidVal.symsCopy_sound
#print axioms Opt.MidVal.checkCertSymsAt_sound
#print axioms Opt.MidVal.checkedSymsAt_simMUAt
#print axioms Link.hoistCopy_sound
#print axioms Link.midPairSymsB_sound
#print axioms Link.midValidatedSymsB_sound
#print axioms Link.midValidatedSymsB_of
#print axioms Link.midEntry_srMUAt
#print axioms Link.midProgAt_sim
#print axioms Link.midProgAt
#print axioms Link.midProgAt_depth
#print axioms E2E.midval_entrySyms
#print axioms E2E.ReturnPinExecBytes.binary_correct_exec_proven_midS
#print axioms E2E.ReturnPinExecBytes.binary_correct_exec_peak_proven_midS
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTS_midS
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS_midS
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_provenT_midS
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT_midS
#print axioms Link.compileExe_correct_sourceMidS
#print axioms Link.compileExe_correct_source_peakMidS
#print axioms Link.DeadCleanup.compileExe_correct_sourceMidS
#print axioms Link.DeadCleanup.compileExe_correct_source_peakMidS
#print axioms Link.compileExeOpt_correct_sourceMidS
#print axioms Link.compileExeOpt_correct_source_peakMidS
#print axioms Link.DeadCleanup.compileExeOpt_correct_sourceMidS
#print axioms Link.DeadCleanup.compileExeOpt_correct_source_peakMidS
#print axioms Link.DeadCleanup.compileExeT_correct_sourceMidS
#print axioms Link.DeadCleanup.compileExeT_correct_source_peakMidS
#print axioms Link.ReturnPinCompilerWith.attempt_correct_sourceMidS
#print axioms Link.ReturnPinCompilerWith.attempt_correct_source_peakMidS
#print axioms Link.SemanticCompilerWith.attempt_correct_sourceMidS
#print axioms Link.SemanticCompilerWith.attempt_correct_source_peakMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakMidS
#print axioms Link.TypedCompilerWith.attempt_correct_sourceMidS
#print axioms Link.TypedCompilerWith.attempt_correct_source_peakMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceTBMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakTBMidS
#print axioms FVTest.Link.MidSymsWitness.facts_true -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.facts_spec -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.real_simAt -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.real_midProgAt -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.fold_simAt -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.real_noSyms_rejected -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.sh_simAt -- witness: native_decide
#print axioms FVTest.Link.MidSymsWitness.keep_empty
#print axioms FVTest.Link.MidSymsWitness.FunSimMUAt.entry_rel
#print axioms FVTest.Link.MidSymsWitness.not_funSimMUAt_ret
#print axioms FVTest.Link.MidSymsWitness.sh_not_simAt
#print axioms FVTest.Link.MidSymsWitness.sh_symsAt_rejected
#print axioms Link.MidSourceWitness.correct_sourceMidS_applies -- witness: native_decide
#print axioms E2E.MidSourceTBWitness.correct_sourceTBMidS_applies -- witness: native_decide
