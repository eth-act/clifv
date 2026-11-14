import FV.Link.ConstPhiPair
import FV.Opt.Proof.ConstPhiWitness
import FV.E2E.ConstPhiE2EWitness
import FV.Link.ConstPhiExeWitness

#print axioms Opt.ConstPhi.cpOk_facts
#print axioms Opt.ConstPhi.CR.isSimW
#print axioms Opt.ConstPhi.cpOk_simX
#print axioms Opt.ConstPhi.run_simX
#print axioms Opt.ConstPhi.CR.isSimWU
#print axioms Opt.ConstPhi.cpOk_simU
#print axioms Opt.ConstPhi.run_simU
#print axioms Opt.ConstPhi.runCore_facts
#print axioms Opt.ConstPhi.run_shape
#print axioms Opt.ConstPhi.run_pair
#print axioms Opt.ConstPhi.Witness.fwd_simU -- witness: native_decide
#print axioms Opt.ConstPhi.Witness.fwd_run_simU -- witness: native_decide
-- #990 PR 4: the end-to-end theorems over a pass, at constant-phi removal
#print axioms E2E.ShapeFacts.trans
#print axioms E2E.inSubset_pass
#print axioms E2E.pass_entry
#print axioms E2E.pass_lift
#print axioms E2E.pass_entryX
#print axioms E2E.pass_liftU
#print axioms E2E.backend_correct_pass
#print axioms E2E.backend_correct_pass_cleanup
#print axioms E2E.backend_correct_pass_finalTCF
#print axioms E2E.backend_correct_pass_cleanup_unwind_any
#print axioms E2E.backend_correct_pass_unwind_any
#print axioms E2E.backend_correct_legal_pass_env_wide
#print axioms E2E.backend_correct_legal_pass_env_wide_cleanup
#print axioms E2E.backend_correct_legal_pass_wide
#print axioms E2E.backend_correct_legal_pass_wide_cleanup
#print axioms E2E.backend_correct_legal_pass_unwind_env_any
#print axioms E2E.backend_correct_legal_pass_unwind_any
#print axioms Opt.ConstPhi.runOpt_simX
#print axioms Opt.ConstPhi.runOpt_simU
#print axioms Opt.ConstPhi.runOpt_shape
#print axioms E2E.ConstPhiE2EWitness.pass_entry_returns
#print axioms E2E.ConstPhiE2EWitness.pass_cleanup_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.pass_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.pass_finalTCF_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.pass_cleanup_unwind_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.pass_unwind_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.legal_pass_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.legal_pass_cleanup_applies -- witness: native_decide
#print axioms E2E.ConstPhiE2EWitness.legal_pass_unwind_applies -- witness: native_decide
-- #990 PR 4: the linked composition
#print axioms E2E.LinkCheck.FnInput.cp_func
#print axioms E2E.LinkCheck.FnInput.cp_pair
#print axioms Link.LinkSpec.cpRel
#print axioms Link.cpRel_prog
#print axioms Link.cpRun
#print axioms Link.cp_lift
#print axioms Link.withSizes_cp
#print axioms Link.ConstPhiExeWitness.source_returns -- witness: native_decide
