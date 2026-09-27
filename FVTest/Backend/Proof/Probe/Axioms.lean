import FV.Backend.Proof.IselProbe
import FV.Backend.Proof.IselFamilyALU

/-! Axiom audit of the isel proofs (`docs/contracts/backend-proof.md`). -/

open Backend.Proof

#print axioms iadd_base_case_correct_32
#print axioms add64_correct
#print axioms rhs_86_64
#print axioms data_program
#print axioms sem_cmp32
#print axioms sem_cset
#print axioms sem_uxtb32
#print axioms sem_and7_32
#print axioms sem_lsr32
#print axioms sem_addi32
#print axioms lowerInstOk_runTerm
#print axioms aluRR_ruleOk
#print axioms iadd_base_case_ok
#print axioms isub_base_case_ok
