import FV.Backend.Proof.LowerSimUCheckTC
import FVTest.Backend.UnwCheckTCWitness
import FV.Link.ExeT
import FV.Link.DeadCleanupExeT
import FV.E2E.LinkScopeInputT
import FV.E2E.LinkScopeInputCleanupT
import FV.E2E.TypedRulesProg
import FVTest.Link.FloatExeT
import FVTest.E2E.FloatTotalT
import FVTest.E2E.FloatCleanupTotalT
import FV.E2E.VerifiableT
import FVTest.E2E.FloatVerifiedW
import FVTest.Link.FloatCompileExeT
import FV.Link.DeadCleanupCompileT
import FV.E2E.FinalTC
import FV.Backend.Proof.IselCtlTryF

-- S11e5 Stage C (#35): the typed scope (float data movement, float parameters and returns)
#print axioms E2E.typedRules_program
#print axioms E2E.LinkCheck.pipeT_okT
#print axioms E2E.LinkCheck.resultsT_ok_inT
#print axioms E2E.LinkCheck.pipeCleanupT_okT
#print axioms E2E.LinkCheck.resultsCleanupT_ok_inT
#print axioms E2E.LinkCheck.resultsCleanupT_ok_input
#print axioms E2E.backend_total_emit_cleanupT
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
#print axioms E2E.InSubsetT.of_verifiableT
#print axioms E2E.verifiable_or_verifiableT_of_unverifiedReason
#print axioms E2E.lowerChecked_spec

-- non-vacuity witnesses
#print axioms E2E.FloatExeTWitness.correctT_spec -- witness: native_decide
#print axioms E2E.FloatExeTWitness.correct_depthT_spec -- witness: native_decide
#print axioms E2E.FloatExeTWitness.correct_peakT_spec -- witness: native_decide
#print axioms E2E.FloatExeTWitness.correctT_specC -- witness: native_decide
#print axioms E2E.FloatExeTWitness.viaT_baseline -- witness: native_decide
#print axioms FloatCleanupTotalT.pipeCleanupT_okT_w -- witness: native_decide
#print axioms FloatCleanupTotalT.resultsCleanupT_ok_inT_w -- witness: native_decide
#print axioms FloatVerifiedW.inSubsetT_w -- witness: native_decide
#print axioms FloatVerifiedW.lowerChecked_w -- witness: native_decide
#print axioms FloatVerifiedW.lowerChecked_mv -- witness: native_decide
#print axioms Link.DeadCleanup.compileExeT_correct
#print axioms Link.DeadCleanup.compileExeT_total_reach_input
#print axioms Link.DeadCleanup.compileExeT_eq
#print axioms E2E.FloatCompileExeTWitness.correct_spec -- witness: native_decide

-- S11e6 slice 2c (#419): direct `try_call` with f32/f64 signatures, per-function typed chain
#print axioms E2E.backend_correct_finalTC
#print axioms E2E.backend_correct_final_exTC
#print axioms E2E.verdict_of_unverifiedReason
#print axioms E2E.lowerChecked_specTC
#print axioms Backend.Proof.tryUnmatchableTC_program
#print axioms Backend.Proof.Driver.tryCallsTC_of_rules
#print axioms Backend.Proof.tryRulesCorrectTFP_program

-- S11e6 #585: the typed-try_call exceptional-edge validator
#print axioms Backend.Proof.Driver.loweringUTC_of_check
#print axioms Backend.Proof.Driver.unwShape_of_okTC
#print axioms Backend.Proof.Driver.tryExnBTC_sound
#print axioms Backend.Proof.Driver.exnArgRegC_int
#print axioms UnwCheckTCWitness.unwCheckTC_true -- witness: native_decide
#print axioms UnwCheckTCWitness.lowerCheckUTC_true -- witness: native_decide
#print axioms UnwCheckTCWitness.unwCheck_false -- witness: native_decide
