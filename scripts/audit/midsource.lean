import FV.Link.MidSource
import FV.Link.MidPair
import FV.Link.MidProg
import FV.Link.MidSourceRoutes
import FV.E2E.MidValExecProven
import FVTest.Link.MidPairWitness

/-! #1119 layer 2: the bundle's program through the mid-end validator. -/

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
#print axioms FVTest.Link.MidPairWitness.facts0 -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.facts_spec -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.validated -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.midProg_applies -- witness: native_decide
#print axioms FVTest.Link.MidPairWitness.keep_empty
