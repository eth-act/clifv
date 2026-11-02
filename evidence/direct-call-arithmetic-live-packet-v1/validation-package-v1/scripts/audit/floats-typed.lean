import FV.Backend.Proof.LowerSimUCheckTC
import FVTest.Backend.UnwCheckTCWitness
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
import FV.Link.DeadCleanupExePeakT
import FVTest.Link.FloatCompileExeTPeak
import FV.Link.DeadCleanupExeSourceT
import FV.Front.ExeT
import FVTest.Link.FloatCompileExeTSource
import FV.E2E.CompiledAnyT
import FV.E2E.PairDriverTC
import FV.E2E.DeadCleanupPairTC
import FV.E2E.DeadCleanupLinkCheckT
import FVTest.Link.FloatTryCompileExeT
import FV.Link.DeadCleanupCompileTFast
import FV.E2E.FinalTCF
import FVTest.E2E.FloatArithFinalTCF
import FVTest.E2E.FloatCmpFinalTCF
import FV.Backend.Proof.LowerContractTPF
import FVTest.Link.FloatArithCompileExeT
import FV.E2E.CompiledAnyTS
import FV.E2E.SemanticPipelineCheckT
import FV.E2E.SemanticExecTS
import FV.Link.SemanticCompileT
import FV.Link.SemanticExeSourceT
import FVTest.Link.FloatStockCompileT
import FVTest.Link.FloatLinkCallsT
import FV.E2E.LinkGoodT

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
#print axioms E2E.LinkCheck.okBCleanupTFast_eq
#print axioms E2E.FloatTryCompileExeTWitness.okBCleanupT_spec -- witness: native_decide
#print axioms E2E.FloatTryCompileExeTWitness.checks_true -- witness: native_decide
#print axioms E2E.FloatTryCompileExeTWitness.correct_spec -- witness: native_decide
#print axioms Backend.Proof.tryRulesCorrectTFP_program

-- S11e6 (#419): typed cleanup peak theorems
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT
#print axioms Link.DeadCleanup.compileExe_correct_peakT
#print axioms Link.DeadCleanup.compileExeT_correct_peak
#print axioms E2E.FloatCompileExeTPeakWitness.correct_peakT_spec -- witness: native_decide
#print axioms E2E.FloatCompileExeTPeakWitness.correct_peakT_specC -- witness: native_decide

-- S11e6 (#419): typed source and frontend theorems (`lean-link --verified` on a typed input)
#print axioms Link.DeadCleanup.compileExe_correct_sourceT
#print axioms Link.DeadCleanup.compileExe_correct_source_peakT
#print axioms Link.DeadCleanup.compileExeT_correct_source
#print axioms Link.DeadCleanup.compileExeT_correct_source_peak
#print axioms Front.bundle_correct_sourceT
#print axioms Front.bundle_correct_source_peakT
#print axioms Front.bundle_correct_rawT
#print axioms Front.bundle_correct_raw_peakT
#print axioms E2E.FloatCompileExeTSourceWitness.source_spec -- witness: native_decide
#print axioms E2E.FloatCompileExeTSourceWitness.source_peak_spec -- witness: native_decide
#print axioms E2E.FloatCompileExeTSourceWitness.sourceT_specC -- witness: native_decide
#print axioms E2E.FloatCompileExeTSourceWitness.source_peakT_specC -- witness: native_decide

-- S11e6 (#419): link layer: world-form per-function theorems, typed try_calls
#print axioms E2E.driverHypTC_relW_of
#print axioms E2E.driverHypTC_relW
#print axioms E2E.iselSim_relWTC
#print axioms E2E.backend_correct_worldTC
#print axioms Backend.Proof.LowerTryOkPC.sem_ext
#print axioms E2E.lowerTryOkC_pair_of
#print axioms E2E.lowerTryOkC_pairF
#print axioms E2E.lowerTryOkC_pairF_value
#print axioms Backend.Proof.tryOkPC_of_rules
#print axioms Backend.Proof.tryOkPC_runTerm
#print axioms E2E.tryCalls_pairTC
#print axioms E2E.vcode_niTC
#print axioms E2E.backend_correct_world_niTC
#print axioms E2E.iselSim_relW_cleanupTC
#print axioms E2E.backend_correct_world_cleanupTC
#print axioms E2E.vcode_ni_valueTC
#print axioms E2E.backend_correct_world_ni_valueTC
#print axioms E2E.backend_correct_worldXTC
#print axioms E2E.backend_correct_world_niXTC
#print axioms E2E.backend_correct_worldX_cleanupTC
#print axioms E2E.backend_correct_world_niX_cleanupTC
#print axioms E2E.backend_correct_world_pipelineTC
#print axioms E2E.backend_correct_world_ni_pipelineTC
#print axioms E2E.backend_correct_worldX_pipelineTC
#print axioms E2E.backend_correct_world_niX_pipelineTC
#print axioms E2E.backend_correct_world_pipelineAnyT
#print axioms E2E.backend_correct_world_ni_pipelineAnyT
#print axioms E2E.backend_correct_worldX_pipelineAnyT
#print axioms E2E.backend_correct_world_niX_pipelineAnyT

-- S11e6 (#419): `compileExeT`'s typed checks at the size of std (equal to the definitions)
#print axioms E2E.LinkCheck.inScopePTPar_eq
#print axioms E2E.LinkCheck.calleeWithB_eq
#print axioms E2E.LinkCheck.outChksTWith_eq
#print axioms E2E.LinkCheck.outOkTRFast_eq
#print axioms Link.DeadCleanup.outOkTFast_eq
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

-- S11e6 #585: the typed-try_call exceptional-edge validator
#print axioms Backend.Proof.Driver.loweringUTC_of_check
#print axioms Backend.Proof.Driver.unwShape_of_okTC
#print axioms Backend.Proof.Driver.tryExnBTC_sound
#print axioms Backend.Proof.Driver.exnArgRegC_int
#print axioms UnwCheckTCWitness.unwCheckTC_true -- witness: native_decide
#print axioms UnwCheckTCWitness.lowerCheckUTC_true -- witness: native_decide
#print axioms UnwCheckTCWitness.unwCheck_false -- witness: native_decide
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

-- S11f (#35): the link-level chain with the proven float operations (compileExeT's third branch
-- admits `Compile.functionETCF`; `LinkSys.OkT.subset` is `InSubsetTCF`)
#print axioms Backend.Proof.lowerInstOkP_of_rulesTF
#print axioms Backend.Proof.lowerInstOkP_runTermTF
#print axioms E2E.driverHypTCF_relW_of
#print axioms E2E.driverHypTCF_relW
#print axioms E2E.iselSim_relWTCF
#print axioms E2E.backend_correct_worldTCF
#print axioms E2E.instCalls_pairTCF
#print axioms E2E.vcode_niTCF
#print axioms E2E.backend_correct_world_niTCF
#print axioms E2E.CompiledCleanupTC.toTCF
#print axioms E2E.CompiledCleanupTCF.toA
#print axioms E2E.outgoing_le_intBaseCleanupATCF
#print axioms E2E.cfg_of_cleanupTCF
#print axioms E2E.driverHypTCF_relW_value
#print axioms E2E.prepareCorrect_cleanupTCF
#print axioms E2E.iselSim_relW_cleanupTCF
#print axioms E2E.backend_correct_world_cleanupTCF
#print axioms E2E.instCalls_pair_valueTCF
#print axioms E2E.vcode_ni_valueTCF
#print axioms E2E.backend_correct_world_ni_valueTCF
#print axioms E2E.CompiledEitherTC.toTCF
#print axioms E2E.CompiledEitherTCF.lowerOk
#print axioms E2E.backend_correct_worldXTCF
#print axioms E2E.backend_correct_world_niXTCF
#print axioms E2E.backend_correct_worldX_cleanupTCF
#print axioms E2E.backend_correct_world_niX_cleanupTCF
#print axioms E2E.backend_correct_world_pipelineTCF
#print axioms E2E.backend_correct_world_ni_pipelineTCF
#print axioms E2E.backend_correct_worldX_pipelineTCF
#print axioms E2E.backend_correct_world_niX_pipelineTCF
#print axioms E2E.hasTls_of_vcodeCleanupATCF
#print axioms E2E.backend_correct_world_pipelineAnyTF
#print axioms E2E.backend_correct_world_ni_pipelineAnyTF
#print axioms E2E.backend_correct_worldX_pipelineAnyTF
#print axioms E2E.backend_correct_world_niX_pipelineAnyTF
-- the TC statements, now corollaries of the TCF ones
#print axioms E2E.driverHypTC_relW_of
#print axioms E2E.driverHypTC_relW
#print axioms E2E.iselSim_relWTC
#print axioms E2E.backend_correct_worldTC
#print axioms E2E.vcode_niTC
#print axioms E2E.backend_correct_world_niTC
#print axioms E2E.driverHypTC_relW_value
#print axioms E2E.iselSim_relW_cleanupTC
#print axioms E2E.backend_correct_world_cleanupTC
#print axioms E2E.vcode_ni_valueTC
#print axioms E2E.backend_correct_world_ni_valueTC
#print axioms E2E.backend_correct_worldXTC
#print axioms E2E.backend_correct_world_niXTC
#print axioms E2E.backend_correct_worldX_cleanupTC
#print axioms E2E.backend_correct_world_niX_cleanupTC
#print axioms E2E.LinkCheck.okRWith_soundT
#print axioms E2E.FloatArithCompileExeTWitness.checks_true -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.okBCleanupT_spec -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.correct_spec -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.compiledTCF_w -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.compiledCleanupTCF_w -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.worldTCF_w -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.world_niX_cleanupTCF_w -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.world_ni_pipelineTCF_w -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.world_pipelineAnyTF_w -- witness: native_decide
#print axioms E2E.FloatArithCompileExeTWitness.world_niX_pipelineAnyTF_w -- witness: native_decide

-- #722: the typed compiler on the Stock route (attemptT; Stock artifacts of integer functions
-- and typed artifacts in one link contract)
#print axioms E2E.retRegsOk_of_x
#print axioms E2E.backend_correct_world_pipelineAnyTS
#print axioms E2E.backend_correct_world_ni_pipelineAnyTS
#print axioms E2E.backend_correct_worldX_pipelineAnyTS
#print axioms E2E.backend_correct_world_niX_pipelineAnyTS
#print axioms E2E.LinkCheck.okRWithTS_soundT
#print axioms E2E.LinkCheck.okRWithTS_eq_fast
#print axioms E2E.SemanticStackBound.okBTS_sound
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTS
#print axioms E2E.SemanticExecBytes.binary_correct_exec_depth_provenTS
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS
#print axioms Link.SemanticCompilerWith.attemptT_spec
#print axioms Link.SemanticCompilerWith.attemptT_correct
#print axioms Link.SemanticCompilerWith.attemptT_correct_depth
#print axioms Link.SemanticCompilerWith.attemptT_correct_peak
#print axioms Link.SemanticCompilerWith.attemptT_correct_source
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peak
#print axioms E2E.FloatStockCompileTWitness.checks_true -- witness: native_decide
#print axioms E2E.FloatStockCompileTWitness.parts -- witness: native_decide
#print axioms E2E.FloatStockCompileTWitness.correct_applies -- witness: native_decide
#print axioms E2E.FloatStockCompileTWitness.source_applies -- witness: native_decide

-- #742: class-aware program call sites in the typed link (OkT.callRegs/blrRegs by class)
#print axioms E2E.LinkCheck.sigRetRegs_length
#print axioms E2E.LinkCheck.sigRetRegs_int
#print axioms E2E.LinkCheck.siteRegsC_of_int
#print axioms E2E.LinkCheck.callRegsC_of_int
#print axioms E2E.LinkCheck.blrOkC_sound
#print axioms E2E.LinkCheck.siteOkC_sound
#print axioms E2E.LinkCheck.siteOkC_reg
#print axioms E2E.LinkCheck.indFastBC_eq
#print axioms E2E.LinkCheck.linkChksWithTS_of
#print axioms E2E.RetsOkT.reg_at
#print axioms E2E.LinkSys.IndSigMatch.sigRets_length
#print axioms E2E.LinkSys.blrRegsC_of_int
#print axioms E2E.LinkSys.progOsCoreT
#print axioms E2E.LinkSys.progResultT
#print axioms E2E.LinkSys.progX_niT
#print axioms E2E.LinkSys.thmT
#print axioms E2E.LinkSys.thmGT
#print axioms E2E.backend_correct_programT
#print axioms E2E.LinkCheck.indFactsRWithTS
#print axioms E2E.FloatLinkCallsTWitness.checks_true -- witness: native_decide
#print axioms E2E.FloatLinkCallsTWitness.parts -- witness: native_decide
