import FV.E2E.SemanticReturnPinsPass
import FVTest.Backend.SemanticReturnPinsPassWitness

-- #1100: the Stock path's theorem composed with i128 legalisation and constant-phi removal
#print axioms E2E.ReturnPinMode.valid_sig
#print axioms E2E.relW_slots
#print axioms E2E.backend_correct_pass_semantic_return_pins
#print axioms E2E.backend_correct_legal_env_wide_semantic_return_pins
#print axioms E2E.backend_correct_legal_wide_semantic_return_pins
#print axioms E2E.backend_correct_legal_pass_env_wide_semantic_return_pins
#print axioms E2E.backend_correct_legal_pass_wide_semantic_return_pins
#print axioms FVTest.Backend.SemanticReturnPinsPassWitness.factsCp0 -- witness: native_decide
#print axioms FVTest.Backend.SemanticReturnPinsPassWitness.premises
#print axioms FVTest.Backend.SemanticReturnPinsPassWitness.pass_applies -- witness: native_decide
