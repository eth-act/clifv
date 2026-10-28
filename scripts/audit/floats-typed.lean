import FV.Link.DeadCleanupCompileT3
import FVTest.E2E.FloatScopeT3
import FVTest.Link.FloatCompileExeT3
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
import FV.E2E.FinalTCF
import FVTest.E2E.FloatArithFinalTCF
import FVTest.E2E.FloatCmpFinalTCF

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

-- the decider-free typed scope fnScopeInTB3 / compileExeT3 (Floats15)
#print axioms E2E.LinkCheck.lowerOutTB_of_T3
#print axioms E2E.LinkCheck.resClassOkB_of_T3
#print axioms E2E.LinkCheck.fnScopeInTB2_of_T3
#print axioms E2E.LinkCheck.inScopeInT_of_T3
#print axioms E2E.LinkCheck.ctlSpillB_of_T3
#print axioms E2E.LinkCheck.ctlInstsB_of_T3
#print axioms E2E.LinkCheck.formsCoveredB_of_T3
#print axioms E2E.LinkCheck.emitCondsB_of_T3
#print axioms E2E.LinkCheck.lowerFunction_ok_T3
#print axioms E2E.LinkCheck.pipeT_okT3
#print axioms E2E.LinkCheck.pipeCleanupT_okT3
#print axioms E2E.LinkCheck.resultsCleanupT_ok_inT3
#print axioms E2E.LinkCheck.inScopePT_of_inT
#print axioms E2E.LinkCheck.inScopePT_of_inT3
#print axioms Link.DeadCleanup.compileExeT3_correct
#print axioms Link.DeadCleanup.compileExeT3_total_reach_input
#print axioms Link.DeadCleanup.compileExeT3_eq
#print axioms FloatScopeT3.checks_w -- witness: native_decide
#print axioms FloatScopeT3.pipeCleanupT_okT3_w -- witness: native_decide
#print axioms FloatScopeT3.inScopePT_w -- witness: native_decide
#print axioms E2E.FloatCompileExeT3Witness.correct_spec -- witness: native_decide

-- S11e6 slice 2c (#419): direct `try_call` with f32/f64 signatures, per-function typed chain
#print axioms E2E.backend_correct_finalTC
#print axioms E2E.backend_correct_final_exTC
#print axioms E2E.verdict_of_unverifiedReason
#print axioms E2E.lowerChecked_specTC
#print axioms Backend.Proof.tryUnmatchableTC_program
#print axioms Backend.Proof.Driver.tryCallsTC_of_rules
#print axioms Backend.Proof.tryRulesCorrectTFP_program

-- S11f (#35): float arithmetic, rounding and conversions in the per-function typed chain
#print axioms E2E.backend_correct_finalTCF
#print axioms E2E.backend_correct_final_exTCF
#print axioms E2E.backend_correct_m4_exTCF
#print axioms E2E.iselSimTCF_of_rules
#print axioms E2E.verdict_of_unverifiedReasonF
#print axioms E2E.lowerChecked_specTCF
#print axioms E2E.InSubsetTCF.of_verifiableTCF
#print axioms E2E.CompiledTC.toTCF
#print axioms Backend.Proof.nonEUnmatchableTF_program
#print axioms Backend.Proof.nonEUnmatchableT_program
#print axioms Backend.Proof.lowerRulesCorrectCvtT_program
#print axioms Backend.Proof.exclOkTF_program
#print axioms Backend.Proof.lower_nonroot_nomatchTF_calls
#print axioms Backend.Proof.lowerInstOk_of_rulesTF
#print axioms Backend.Proof.instCallsTF_of_rules
#print axioms Backend.Proof.Driver.instCallsT_of_rules
#print axioms Backend.Proof.Driver.loweringTCF_of_check
#print axioms Backend.Proof.Driver.lowerCheckTCF_of_lowerCheckTC
#print axioms Backend.Proof.Driver.instScopeT_of_lowerCheckTC
#print axioms Compile.functionETCF_of_functionETC
#print axioms FloatArithFinalTCF.verdict_f -- witness: native_decide
#print axioms FloatArithFinalTCF.backend_correct_finalTCF_fOps -- witness: native_decide

-- S11f (#35): scalar `fcmp` in the per-function typed chain
#print axioms Backend.Proof.rule_lower_2179_nomatchT
#print axioms Backend.Proof.lower_rule952_filter
#print axioms Backend.Proof.fCmpET_cases
#print axioms Backend.Proof.instData_cmp
#print axioms Backend.Proof.fcmp_resTy
#print axioms Backend.Proof.cmpNames_idx
#print axioms Backend.Proof.cmpNames_neI
#print axioms Backend.Proof.inst_splitF1_calls
#print axioms Backend.Proof.nonE_splitF
#print axioms Backend.Proof.nonEOkF_program
#print axioms Backend.Proof.lowerRulesCorrectFC_program
#print axioms Backend.Proof.lowerInstOk_runTermTF
#print axioms FloatCmpFinalTCF.fcmp_excl_w -- witness: native_decide
#print axioms FloatCmpFinalTCF.verdict_f -- witness: native_decide
#print axioms FloatCmpFinalTCF.backend_correct_finalTCF_fCmp -- witness: native_decide
