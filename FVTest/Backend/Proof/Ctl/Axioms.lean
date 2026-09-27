import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlBranch
import FV.Backend.Proof.IselCtlCall

/-! Axiom audit of the control-flow family (Ctl). -/

#print axioms Backend.Proof.lowerTermRulesCorrect
#print axioms Backend.Proof.termUnmatchable
#print axioms Backend.Proof.branchExcludedUnmatchable
#print axioms Backend.Proof.jump_ruleOk
#print axioms Backend.Proof.trap_ruleOk
#print axioms Backend.Proof.ret_ruleOk
