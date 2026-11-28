import FV.Link.MidSourceRoutesSyms
import FV.Link.MidSourceTBSyms
import FV.Link.TypedCompileSourceCp
import FV.E2E.MidValExecProvenR
import FV.E2E.StaticShareR
import FVTest.Link.CallRegsR4Witness

-- #753 stage R4: the typed Stock route with the register-guarded calls. Stage R3' (the per-state
-- facts keep the guarded call premise), stage R2X' (the X world chain with them), the checks
-- `okRWithTSR` and the link contract `LinkSys.OkTR`, the R chain up to the binary theorems, the
-- compilers switched to `okRWithTSR` (the `…_correct*` theorems with their texts, re-proved), the
-- three changed texts and the witnesses.

-- R3': per-state facts with the guarded call premise.
#print axioms Backend.Proof.RL.noCall_le
#print axioms Backend.Proof.RL.noCall_callPre
#print axioms Backend.Proof.RL.GoodXR.callR
#print axioms Backend.Proof.actGoodXR.of_noCallSites
#print axioms Backend.Proof.realizes_callRG
#print axioms Backend.Proof.realizes_tryCallRG
#print axioms Backend.Proof.realizes_stepRG
#print axioms Backend.Proof.realizes_allRG
#print axioms Backend.Proof.regLevelCorrect_worldXRG
#print axioms Backend.Proof.regLevelCorrect_worldX_valueRG
#print axioms Backend.Proof.regLevelRG

-- R2X': the X world theorems with the guarded per-state facts.
#print axioms E2E.backend_correct_worldX_pipelineAnyTSRG
#print axioms E2E.backend_correct_world_niX_pipelineAnyTSRG
#print axioms E2E.backend_correct_worldX_pipelineRG
#print axioms E2E.backend_correct_world_niX_pipelineRG

-- R4 checks: the `blr` site's shape, the return classes, no call sites, `okRWithTSR`.
#print axioms E2E.LinkCheck.blrShapeB_sound
#print axioms E2E.LinkCheck.siteOkCR_sym_sound
#print axioms E2E.LinkCheck.siteOkCR_reg
#print axioms E2E.LinkCheck.retClsB_sound
#print axioms E2E.LinkCheck.noCallSitesB_sound
#print axioms E2E.LinkCheck.linkChksWithTSXR_of
#print axioms E2E.LinkCheck.lowerOkTSRB_sound
#print axioms E2E.LinkCheck.CompiledSemanticNIR.of_checksR
#print axioms E2E.LinkCheck.okRWithTSR_eq_fast
#print axioms E2E.LinkCheck.okRWithTSR_soundTR
#print axioms E2E.LinkCheck.withTSROfNI_eq

-- The link contract `OkTR`: the register premises from the link's declarations, the R chain.
#print axioms E2E.LinkSys.regCompatGotR
#print axioms E2E.LinkSys.regCompatIndR
#print axioms E2E.LinkSys.progOsRegTR
#print axioms E2E.LinkSys.calleeTryOkTR
#print axioms E2E.LinkSys.thmTR
#print axioms E2E.LinkSys.callGoodTR
#print axioms E2E.LinkSys.thmGTR
#print axioms E2E.backend_correct_program_coreTR
#print axioms E2E.backend_correct_program_budgetTR
#print axioms E2E.backend_correct_program_coreXTR
#print axioms E2E.backend_correct_program_peakXTR
#print axioms E2E.SemanticStackBound.okBTS_soundR
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTSR
#print axioms E2E.SemanticExecBytes.binary_correct_exec_depth_provenTSR
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTSR
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTSR_mid
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTSR_mid
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTSR_midS
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTSR_midS
#print axioms E2E.SemanticBinary.trapsExplicit_of_runTSR
#print axioms E2E.SemanticBinary.trapsExplicit_of_runDTSR

-- The compilers on `okRWithTSR`: the theorems with their texts, re-proved.
#print axioms Link.SemanticCompilerWith.attemptT_eq_fast
#print axioms Link.SemanticCompilerWith.attemptT_correct
#print axioms Link.SemanticCompilerWith.attemptT_correct_depth
#print axioms Link.SemanticCompilerWith.attemptT_correct_peak
#print axioms Link.SemanticCompilerWith.attemptT_correct_source
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peak
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceTB
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakTB
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceCp
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakCp
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceTBMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakTBMid
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceTBMidS
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakTBMidS
#print axioms Link.TypedCompilerWith.attempt_eq_fast
#print axioms Link.TypedCompilerWith.attempt_correct
#print axioms Link.TypedCompilerWith.attempt_correct_depth
#print axioms Link.TypedCompilerWith.attempt_correct_peak
#print axioms Link.TypedCompilerWith.attempt_correct_source
#print axioms Link.TypedCompilerWith.attempt_correct_source_peak
#print axioms Link.TypedCompilerWith.attempt_correct_sourceCp
#print axioms Link.TypedCompilerWith.attempt_correct_source_peakCp
#print axioms Link.TypedCompilerWith.attempt_cleanup_eq
#print axioms Link.TypedStockShared.attemptTFrom_eq
#print axioms Link.TypedStockShared.stockFailsR_isEmpty

-- The three changed texts (rule (a)).
#print axioms Link.SemanticCompilerWith.attemptT_spec
#print axioms Link.TypedCompilerWith.attempt_spec
#print axioms Link.TypedStockShared.attemptTFrom_stockFails

-- Witnesses: the old texts are false; `attemptT_correct` applies to a vtable-site function; the
-- sret/x8 mismatch is not entered (guard, `abiMatch`) or left out (`declSig`).
#print axioms E2E.CallRegsR4Witness.checks_true -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.parts -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.attemptT_spec_old_false -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.attempt_spec_old_false -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.attemptTFrom_stockFails_old_false -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.correct_applies -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.sigs_parsed -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.mismatch_regs -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.mismatch_guard_false -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.mismatch_abiMatch -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.checksBad_true -- witness: native_decide
#print axioms E2E.CallRegsR4Witness.mismatch_left_out -- witness: native_decide
