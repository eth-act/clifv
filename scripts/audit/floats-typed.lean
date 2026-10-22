import FV.Link.ExeT
import FV.Link.DeadCleanupExeT
import FV.E2E.LinkScopeInputT
import FV.E2E.TypedRulesProg
import FVTest.Link.FloatExeT
import FVTest.E2E.FloatTotalT

-- S11e5 Stage C (#35): the typed scope (float data movement, float parameters and returns)
#print axioms E2E.typedRules_program
#print axioms E2E.LinkCheck.pipeT_okT
#print axioms E2E.LinkCheck.resultsT_ok_inT
#print axioms E2E.LinkCheck.inScopeInT_of_inScopeIn
#print axioms E2E.LinkCheck.inScopePT_of_inScopeP
#print axioms E2E.LinkCheck.outOkT_of_inScopeP
#print axioms E2E.LinkCheck.outOkTCleanup_of_inScopeP
#print axioms E2E.LinkCheck.okT_of_inScopeT
#print axioms E2E.LinkCheck.okT_of_inScopeCleanupT
#print axioms Link.compileExe_correctT
#print axioms Link.compileExe_correct_depthT
#print axioms Link.compileExe_correct_peakT
#print axioms Link.compileExe_correct_viaT
#print axioms Link.compileExe_correct_depth_viaT
#print axioms Link.compileExe_correct_peak_viaT
#print axioms Link.DeadCleanup.compileExe_correctT
#print axioms Link.DeadCleanup.compileExe_correct_viaT

-- non-vacuity witnesses
#print axioms E2E.FloatExeTWitness.correctT_spec -- witness: native_decide
#print axioms E2E.FloatExeTWitness.correct_depthT_spec -- witness: native_decide
#print axioms E2E.FloatExeTWitness.correct_peakT_spec -- witness: native_decide
#print axioms E2E.FloatExeTWitness.correctT_specC -- witness: native_decide
#print axioms E2E.FloatExeTWitness.viaT_baseline -- witness: native_decide
