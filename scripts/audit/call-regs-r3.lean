import FV.E2E.CompiledAnyTSRM6

-- #753 stage R3: M6 for the register-guarded semantics (`RegLevelR`, the premise `hM6` of stage
-- R2's world theorems) proved (`regLevelR`), and the four R2 world theorems with it discharged.

-- M6 for the register-guarded semantics and its four statements.
#print axioms Backend.Proof.regLevelR
#print axioms Backend.Proof.regLevelCorrect_worldR
#print axioms Backend.Proof.regLevelCorrect_worldXR
#print axioms Backend.Proof.regLevelCorrect_world_valueR
#print axioms Backend.Proof.regLevelCorrect_worldX_valueR

-- The R2 world theorems without the M6 premise.
#print axioms E2E.backend_correct_world_pipelineAnyTSRM6
#print axioms E2E.backend_correct_world_ni_pipelineAnyTSRM6
#print axioms E2E.backend_correct_worldX_pipelineAnyTSRM6
#print axioms E2E.backend_correct_world_niX_pipelineAnyTSRM6

-- The realisation at the register-guarded semantics.
#print axioms Backend.Proof.realizes_op_coreX_sem
#print axioms Backend.Proof.realizes_callR
#print axioms Backend.Proof.realizes_tryCallR
#print axioms Backend.Proof.realizes_stepR
#print axioms Backend.Proof.realizes_allR
#print axioms Backend.Proof.realizes_value_allR
#print axioms Backend.Proof.regLevelCorrect_world_atXR
#print axioms Backend.Proof.regLevelCorrect_world_atX_valueR
