import FV.Link.ExeLd
import FV.Link.DeadCleanupExeLd
import FV.Link.Ld.LayoutProof
import FV.Link.Ld.LayoutTotal
import FV.Link.Ld.RelocTotal

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

-- the planner meets its plan's conditions by construction (A1a, #409)
#print axioms Link.Ld.layout_okB
#print axioms Link.Ld.assemble_layout
#print axioms Link.Ld.PInv_layPre
#print axioms Link.Ld.pieces_pairwise
#print axioms Link.Ld.tinyLayout_okB -- witness: native_decide

-- the planner accepts its resolved inputs when their references resolve (A1b, #409)
#print axioms Link.Ld.layout_ok
#print axioms Link.Ld.value_ok
#print axioms Link.Ld.layout_ok_witness -- witness: native_decide

-- the body of lean-ld's plan is built when its relocations apply (A1c, #409)
#print axioms Link.Ld.relocVal_ok
#print axioms Link.Ld.buildBody_layout
#print axioms Link.Ld.assemble_layout_ok
#print axioms Link.Ld.tinyPiece_relsOk

-- symbol values in address-free intervals; the relocation checks are sound (A1c, #409)
#print axioms Link.Ld.value_in
#print axioms Link.Ld.relocOkB_of
#print axioms Link.Ld.relIn_relocOkB
