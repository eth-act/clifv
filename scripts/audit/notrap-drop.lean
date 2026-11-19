import FV.E2E.NotrapDropE2E
import FV.Opt.Proof.NotrapDropKeep
import FV.Opt.Proof.NotrapDropWitness

-- option D (#1017, #140): the drop of unused `notrap` loads (Cranelift 0.136.1)
#print axioms Clif.evalInst_notrap_load
#print axioms Opt.NotrapDrop.facts_of
#print axioms Opt.NotrapDrop.evalInst_droppable
#print axioms Opt.NotrapDrop.isSimW
#print axioms Opt.NotrapDrop.dropWith_simX
#print axioms Opt.NotrapDrop.run_simX
#print axioms Opt.NotrapDrop.isSimWU
#print axioms Opt.NotrapDrop.dropWith_simU
#print axioms Opt.NotrapDrop.run_simU
#print axioms Opt.NotrapDrop.dropWith_shape
#print axioms Opt.NotrapDrop.run_shape
#print axioms Opt.NotrapDrop.run_keeps_effects
#print axioms Opt.NotrapDrop.run_keeps_trapping
#print axioms Opt.NotrapDrop.run_keeps_used
#print axioms Opt.NotrapDrop.runCp_simX
#print axioms Opt.NotrapDrop.runCp_simU
#print axioms Opt.NotrapDrop.runCp_shape
#print axioms Opt.NotrapDrop.runCpOpt_simX
#print axioms Opt.NotrapDrop.runCpOpt_simU
#print axioms Opt.NotrapDrop.runCpOpt_shape
#print axioms Opt.NotrapDrop.run_pair
#print axioms Opt.NotrapDrop.runCp_pair
#print axioms Opt.NotrapDrop.Witness.chain_run_simU -- witness: native_decide
#print axioms Opt.NotrapDrop.Witness.liveAddr_simX -- witness: native_decide
#print axioms Opt.NotrapDrop.Witness.trapping_run -- witness: native_decide
#print axioms Opt.NotrapDrop.Witness.used_run -- witness: native_decide
