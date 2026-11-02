import FV.Link.TailExeLd

-- self tail calls as loops (S8a, #32; docs/contracts/e2e.md "Self tail calls as loops")
#print axioms Opt.TailLoop.TailRel.refines
#print axioms Opt.TailLoop.step_rel
#print axioms Opt.TailLoop.run_rel
#print axioms Link.DeadCleanup.compileExeTail_correct
#print axioms Link.DeadCleanup.compileExeTail_correct_peak
#print axioms Link.DeadCleanup.compileExeTail_total_reach_input
#print axioms Link.DeadCleanup.compileExeTail_total_ld
