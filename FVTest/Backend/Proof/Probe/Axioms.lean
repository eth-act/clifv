import FV.Backend.Proof.IselProbe

/-! Axiom audit of the isel probe (`docs/contracts/backend-proof.md`). -/

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
