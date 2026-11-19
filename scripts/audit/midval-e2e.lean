import FV.E2E.MidValPass
import FV.E2E.MidValPassLegacy
import FVTest.Backend.MidValPassWitness

-- #1119 plumbing layer 1: the per-function theorems through the mid-end validator
#print axioms E2E.envKeepsSymbolsX_toX
#print axioms E2E.outcomeRefines_of_toX
#print axioms E2E.midval_sr
#print axioms E2E.midval_entry
#print axioms E2E.midval_entryX
#print axioms E2E.backend_correct_midval_semantic_return_pins
#print axioms E2E.backend_correct_midval_pass_semantic_return_pins
#print axioms E2E.backend_correct_midval_legal_wide_semantic_return_pins
#print axioms E2E.backend_correct_midval_legal_pass_wide_semantic_return_pins
#print axioms E2E.armRefinesLegalU_of_outcome
#print axioms E2E.backend_correct_midval_final_cleanup
#print axioms E2E.backend_correct_midval_pass_cleanup
#print axioms E2E.backend_correct_midval_legal_wide_cleanup
#print axioms E2E.backend_correct_midval_legal_pass_wide_cleanup
#print axioms E2E.backend_correct_midval_final_cleanup_unwind_any
#print axioms E2E.backend_correct_midval_pass_cleanup_unwind_any
#print axioms E2E.backend_correct_midval_legal_unwind_any
#print axioms E2E.backend_correct_midval_legal_pass_unwind_any
#print axioms E2E.backend_correct_midval_final_cleanupT
#print axioms E2E.backend_correct_midval_world_cleanupTCF
#print axioms E2E.backend_correct_midval_world_cleanupTC
#print axioms FVTest.Backend.MidValPassWitness.premises -- witness: native_decide
#print axioms FVTest.Backend.MidValPassWitness.midval_applies -- witness: native_decide
