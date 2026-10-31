import FV.E2E.IndStackWitness
import FV.E2E.DeadCleanupTrapCall
import FV.E2E.LinkArmT
import FV.E2E.TypedRulesProg
import FV.Backend.Proof.IselCtlTryTI

-- S5 (#29): stack-passed arguments of call_indirect / try_call_indirect
#print axioms Backend.Proof.indRulesCorrectP
#print axioms Backend.Proof.indRulesCorrect
#print axioms Backend.Proof.tryIndRulesCorrectP
#print axioms Backend.Proof.tryIndRulesCorrect
#print axioms Backend.Proof.indRulesCorrectTP_program
#print axioms Backend.Proof.indRulesCorrectT_program
#print axioms Backend.Proof.tryIndRulesCorrectTP_program
#print axioms Backend.Proof.tryIndRulesCorrectT_program
#print axioms Backend.Proof.indStack_of_check
#print axioms Backend.Proof.indStackT_of_check
#print axioms Backend.Proof.xCallsIndOk_of_regArgs
#print axioms Backend.indSigsAbiOk_of_indSigsOk
#print axioms E2E.InSubset.of_regArgs
#print axioms E2E.InSubset.of_verifiable
#print axioms E2E.xTrapsOk_of_regArgs
#print axioms E2E.LinkSys.IndSigMatch.paramBytes
#print axioms E2E.LinkSys.argsAt_of_tyMatch
#print axioms E2E.backend_correct_final
#print axioms E2E.backend_correct_final_cleanup_trapcall
#print axioms E2E.IndStackWitness.backend_correct_final_ind_stack
