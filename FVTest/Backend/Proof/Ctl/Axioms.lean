module

public import FV.Backend.Proof.IselCtl
public import FV.Backend.Proof.IselCtlBranch
public import FV.Backend.Proof.IselCtlCall

@[expose] public section

/-! Axiom audit of the control-flow family (Ctl). -/

#print axioms Backend.Proof.lowerTermRulesCorrect
#print axioms Backend.Proof.termUnmatchable
#print axioms Backend.Proof.branchExcludedUnmatchable
#print axioms Backend.Proof.jump_ruleOk
#print axioms Backend.Proof.trap_ruleOk
#print axioms Backend.Proof.ret_ruleOk
#print axioms Backend.Proof.callRulesCorrect
#print axioms Backend.Proof.brif_ruleOk
#print axioms Backend.Proof.tbnz_ruleOk
#print axioms Backend.Proof.tbz_ruleOk
#print axioms Backend.Proof.brTable_ruleOk
#print axioms Backend.Proof.branchRulesCorrect
