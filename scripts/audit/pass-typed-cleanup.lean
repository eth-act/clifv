import FV.E2E.PassTypedCleanup
import FVTest.Backend.TypedPassWitness

-- #1112: the typed theorems composed with i128 legalisation and constant-phi removal
#print axioms E2E.armRefinesLegalT_of
#print axioms E2E.legal_refines_wide
#print axioms E2E.backend_correct_pass_final_cleanupT
#print axioms E2E.backend_correct_pass_world_cleanupTCF
#print axioms E2E.backend_correct_pass_world_cleanupTC
#print axioms E2E.backend_correct_legal_wide_final_cleanupT
#print axioms E2E.backend_correct_legal_wide_world_cleanupTCF
#print axioms E2E.backend_correct_legal_wide_world_cleanupTC
#print axioms E2E.backend_correct_legal_pass_wide_final_cleanupT
#print axioms E2E.backend_correct_legal_pass_wide_world_cleanupTCF
#print axioms E2E.backend_correct_legal_pass_wide_world_cleanupTC
#print axioms FVTest.Backend.TypedPassWitness.receipts_true -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.factsT
#print axioms FVTest.Backend.TypedPassWitness.factsTC
#print axioms FVTest.Backend.TypedPassWitness.factsTCF
#print axioms FVTest.Backend.TypedPassWitness.pass_final_cleanupT_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.pass_world_cleanupTCF_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.pass_world_cleanupTC_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.legal_wide_final_cleanupT_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.legal_wide_world_cleanupTCF_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.legal_wide_world_cleanupTC_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.legal_pass_wide_final_cleanupT_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.legal_pass_wide_world_cleanupTCF_applies -- witness: native_decide
#print axioms FVTest.Backend.TypedPassWitness.legal_pass_wide_world_cleanupTC_applies -- witness: native_decide
