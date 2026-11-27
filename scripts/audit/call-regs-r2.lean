import FV.E2E.CompiledAnyTSR
import FV.E2E.TypedRulesSR

-- #753 stage R2: the register-guarded semantics (RegLevelDriverSemR), the contracts with registers
-- for every base semantics, ActEntryR and the M6 premise RegLevelR (LinkWorldR), and the world
-- theorems at the register-guarded semantics up to the typed link layer's four
-- `…_pipelineAnyTSR` (CompiledAnyTSR).

-- The four end theorems.
#print axioms E2E.backend_correct_world_pipelineAnyTSR
#print axioms E2E.backend_correct_world_ni_pipelineAnyTSR
#print axioms E2E.backend_correct_worldX_pipelineAnyTSR
#print axioms E2E.backend_correct_world_niX_pipelineAnyTSR

-- The artifact contract and the Stock route's bridge.
#print axioms E2E.CompiledSemanticNIR.toNI
#print axioms E2E.CompiledAnyTSR.toTS
#print axioms E2E.ActEntryR.toActEntry
#print axioms E2E.ActEntry.toR

-- The register guard and the contracts with registers.
#print axioms Backend.Proof.regG_mono
#print axioms E2E.lockstep_regG
#print axioms Backend.Proof.callsRefinePR_csemR
#print axioms Backend.Proof.indCallsRefinePR_csemR
#print axioms E2E.callsRefinePR_csemG
#print axioms E2E.indCallsRefinePR_csemG
#print axioms E2E.callsRefinePR_csemGF
#print axioms E2E.indCallsRefinePR_csemGF
#print axioms Backend.DeadCleanup.callsRefinePR_valueSem
#print axioms Backend.DeadCleanup.indCallsRefinePR_valueSem
#print axioms E2E.callsRefinePR_valueSemG
#print axioms E2E.indCallsRefinePR_valueSemG
#print axioms E2E.callsRefinePR_valueSemGF
#print axioms E2E.indCallsRefinePR_valueSemGF

-- The dispatchers and the typed indirect families with registers.
#print axioms Backend.Proof.Driver.instCallsR_of_rules
#print axioms Backend.Proof.Driver.instCallsTR_of_rules
#print axioms Backend.Proof.instCallsTFSOR_of_rules
#print axioms Backend.Proof.Driver.tryCallsTCR_of_rules
#print axioms Backend.Proof.Driver.tryIndCallsTRS_of_rules
#print axioms Backend.Proof.indRulesCorrectTPRS_program
#print axioms Backend.Proof.tryIndRulesCorrectTPRS_program
#print axioms Backend.Proof.tryOkPCR_runTerm

-- CLIF → VCode at the register-guarded semantics.
#print axioms E2E.iselSim_relWR
#print axioms E2E.iselSim_relWTR
#print axioms E2E.iselSim_relWTCFR
#print axioms E2E.iselSim_relW_validatedR
#print axioms E2E.iselSim_relW_cleanup_stageR
#print axioms E2E.iselSim_relW_cleanupT_stageR
#print axioms E2E.iselSim_relW_cleanupTCFR
#print axioms E2E.iselSim_relW_cleanup_validated_stageR

-- Non-interference of the VCode runs.
#print axioms E2E.vcode_niR
#print axioms E2E.vcode_niTR
#print axioms E2E.vcode_niTCFR
#print axioms E2E.vcode_ni_validatedR
#print axioms E2E.vcode_ni_value_stageR
#print axioms E2E.vcode_ni_valueT_stageR
#print axioms E2E.vcode_ni_valueTCFR
#print axioms E2E.vcode_ni_value_validated_stageR

-- The per-state world theorems of every artifact.
#print axioms E2E.backend_correct_worldXR
#print axioms E2E.backend_correct_world_niXR
#print axioms E2E.backend_correct_worldX_cleanupR
#print axioms E2E.backend_correct_world_niX_cleanupR
#print axioms E2E.backend_correct_worldX_pipelineR
#print axioms E2E.backend_correct_world_niX_pipelineR
#print axioms E2E.backend_correct_worldXTR
#print axioms E2E.backend_correct_world_niXTR
#print axioms E2E.backend_correct_worldX_cleanupTR
#print axioms E2E.backend_correct_world_niX_cleanupTR
#print axioms E2E.backend_correct_worldX_pipelineTR
#print axioms E2E.backend_correct_world_niX_pipelineTR
#print axioms E2E.backend_correct_worldXTCFR
#print axioms E2E.backend_correct_world_niXTCFR
#print axioms E2E.backend_correct_worldX_cleanupTCFR
#print axioms E2E.backend_correct_world_niX_cleanupTCFR
#print axioms E2E.backend_correct_worldX_pipelineTCFR
#print axioms E2E.backend_correct_world_niX_pipelineTCFR
#print axioms E2E.backend_correct_worldX_pipelineAnyTFR
#print axioms E2E.backend_correct_world_niX_pipelineAnyTFR
#print axioms E2E.backend_correct_worldX_validatedR
#print axioms E2E.backend_correct_world_niX_validatedR
#print axioms E2E.backend_correct_worldX_cleanup_validatedR
#print axioms E2E.backend_correct_world_niX_cleanup_validatedR
#print axioms E2E.backend_correct_worldX_productionR
#print axioms E2E.backend_correct_world_niX_productionR

-- The world theorems of the earlier R2 modules (LinkWorldR, LinkWorldTR, LinkWorldTCR).
#print axioms E2E.backend_correct_worldR
#print axioms E2E.backend_correct_worldTR
#print axioms E2E.backend_correct_worldTCFR
