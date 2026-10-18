import FV.Link.ExeLd
import FV.Link.DeadCleanupExeLd

-- the executable compiler's totality on `lean-ld`'s output (L2b stage 3e)
#print axioms Link.compileExe_total_ld
#print axioms Link.compileExeOpt_total_ld
#print axioms Link.DeadCleanup.compileExe_total_ld
#print axioms Link.DeadCleanup.compileExeOpt_total_ld
#print axioms Link.Ld.file0OkB_ld
#print axioms Link.Ld.file0OkB_assemble
#print axioms Link.Ld.dataFastB_plan
#print axioms Link.Ld.staticB_phdrs
#print axioms Link.Ld.regionPhsB_plan
#print axioms Link.Ld.tpOff_phdrs
#print axioms Link.Ld.link_ok
#print axioms Link.Ld.itemsB_sound
#print axioms Link.Ld.phdrs_rd
#print axioms Link.Ld.staticB_phdrs_witness
#print axioms Link.Ld.regionPhsB_plan_witness
#print axioms Link.Ld.file0OkB_assemble_witness -- witness: native_decide
#print axioms Link.Ld.dataFastB_plan_witness -- witness: native_decide
