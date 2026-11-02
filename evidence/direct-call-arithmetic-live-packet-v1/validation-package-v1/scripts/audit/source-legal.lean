import FV.Link.ExeSource
import FV.Link.NonVacuityExeSource
import FV.E2E.NonVacuityLegalProgram
import FV.E2E.NonVacuityLegalSource
import FV.E2E.DeadCleanupLegalDirect
#print axioms Link.compileExe_correct_source
#print axioms Link.prog_eq_legal
#print axioms E2E.LegalProgram.legalProg_refines
#print axioms Clif.unlink_run
#print axioms Clif.unlink_steps
#print axioms E2E.LinkCheck.FnInput.func_eq
#print axioms E2E.LinkCheck.LinkInput.prog_eq
#print axioms E2E.LinkCheck.srcCtx
#print axioms Opt.Legal.check_refines2
#print axioms Opt.Legal.check_refines
#print axioms Opt.Legal.legalize_refines2
#print axioms Opt.Legal.Complete.preB_iff
#print axioms Opt.Legal.Complete.check_complete_of_preB
#print axioms Link.SourceWitness.compileExe_correct_source_helper
#print axioms Link.SourceWitness.baseOk_helper
#print axioms Link.SourceWitness.helperOk
#print axioms E2E.LegalProgram.Witness.ctx
#print axioms E2E.LegalProgram.Witness.plain_refines
#print axioms E2E.LegalProgram.Witness.add_refines
#print axioms E2E.LinkCheck.SrcScopeWitness.mixed_in -- witness: native_decide
#print axioms E2E.LinkCheck.SrcScopeWitness.mixed_prog_ne -- witness: native_decide
#print axioms E2E.LinkCheck.SrcScopeWitness.declSig_out -- witness: native_decide
