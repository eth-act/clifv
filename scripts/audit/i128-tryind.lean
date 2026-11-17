import FV.Opt.Proof.LegalSimX2T
import FV.Opt.Proof.LegalPreT
import FV.E2E.LegalProgramT
import FV.E2E.LegalDepthT
import FV.E2E.LegalProgXT
import FV.E2E.LegalSourceT
import FV.Link.SemanticExeSourceTB
import FV.E2E.LegalUnwindTWitness
import FVTest.Link.I128TryIndT

-- #1076: `i128` functions with a `try_call_indirect` (`legalOkTB`, `SrcScopeTB`)
#print axioms Opt.Legal.X.raise_sim
#print axioms Opt.Legal.X.sim_try_raise
#print axioms Opt.Legal.X.sim_try_raise2
#print axioms Opt.Legal.X.sim_tryInd_raise2
#print axioms Opt.Legal.X.sim_callInd_raise2T
#print axioms Opt.Legal.X.sim_runX2T
#print axioms Opt.Legal.X.checkW_refinesX2T
#print axioms Opt.Legal.X.checkW_refinesXT
#print axioms Opt.Legal.X.EnvOkX.twoT
#print axioms Opt.Legal.X.EnvOkX2.toT
#print axioms Opt.Legal.S.sim_tryInd
#print axioms Opt.Legal.S.step_sim_outT
#print axioms Opt.Legal.exnOkT_of_exnOk
#print axioms Opt.Legal.Complete.legalOkTB_cases
#print axioms Opt.Legal.Complete.legalOkTB_of_legalOkB
#print axioms Opt.Legal.legalize_refines2W
#print axioms E2E.LegalProgram.legalFactsT
#print axioms E2E.LegalProgram.ProgCtx.toT
#print axioms E2E.LegalProgram.legalProg_refinesT
#print axioms E2E.LegalProgram.legalProg_refines_depthT
#print axioms E2E.LegalProgram.legalProg_refinesXT
#print axioms E2E.LinkCheck.srcCtxT
#print axioms E2E.LinkCheck.srcScopeTB_of_srcScopeB
#print axioms Link.SemanticCompilerWith.attemptT_correct_sourceTB
#print axioms Link.SemanticCompilerWith.attemptT_correct_source_peakTB
#print axioms Clif.Rust.LegalXTWitness.refines
#print axioms Clif.Rust.LegalXTWitness.caught
#print axioms Clif.Rust.LegalXTWitness.domains -- witness: native_decide
#print axioms E2E.I128TryIndTWitness.correct_source_applies -- witness: native_decide
