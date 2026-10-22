import FV.Concurrency
import FVTest.Concurrency.Litmus
import FVTest.Concurrency.LitmusFull

-- the memory-model layer (T2, #38; docs/plans/atomics.md)
#print axioms Concurrency.Armv8.atomics_sc
#print axioms Concurrency.Armv8.ob_dmb
#print axioms Concurrency.Armv8.hb_shape
#print axioms Concurrency.Armv8.coherence
#print axioms Concurrency.Armv8.atomicity
#print axioms Concurrency.ClifMM.drf_sc
#print axioms Concurrency.Mapping.armv8_to_clif
#print axioms Concurrency.Mapping.armv8_drf_sc
#print axioms Concurrency.Exec.sc_interleaving
#print axioms Concurrency.Mapping.armv8_interleaving
#print axioms Concurrency.Code.lines_kinds
#print axioms Concurrency.Code.ordered_only_atomic
#print axioms Concurrency.Code.memInsns_rmwLoopLines
#print axioms Concurrency.Code.memInsns_casLoopLines
#print axioms Concurrency.Code.kinds_prologueLines
#print axioms Concurrency.Code.kinds_epilogueLines
#print axioms Concurrency.Code.kinds_relaxLines
-- per-thread event semantics of the Arm model (T2d, #302)
#print axioms Concurrency.ArmFoot.exec_nonldst
#print axioms Concurrency.ArmFoot.stepi_setMem
#print axioms Concurrency.ArmFoot.readM_writeM
#print axioms Concurrency.ArmFoot.readM_full_inj
#print axioms Concurrency.ArmThread.step_sc
#print axioms Concurrency.ArmThread.step_mem
#print axioms Concurrency.ArmThread.no_xfail_sc
#print axioms Concurrency.ArmThread.run_sc
#print axioms Concurrency.ArmThread.run_sc_stepi
#print axioms Concurrency.ArmThread.exists_step_sc
#print axioms Concurrency.ArmThread.exists_run_sc
#print axioms Concurrency.ArmThread.footprint_nonldst
#print axioms Concurrency.ArmThread.footprint_dmb
#print axioms Concurrency.ArmThread.footprint_load_excl
#print axioms Concurrency.ArmThread.footprint_store_excl
-- program level (T2e, #303)
#print axioms Concurrency.Prog.drf_sc_init
#print axioms Concurrency.Prog.sc_of_rank_on
#print axioms Concurrency.Prog.replay
#print axioms Concurrency.ClifThread.mrun_mt
#print axioms Concurrency.ProgE2E.wfC
#print axioms Concurrency.ProgE2E.consistentC
#print axioms Concurrency.ProgE2E.program_correct
-- RC11 and cg_clif's strengthening (T2f, #304)
#print axioms Concurrency.RC11.psc_mono
#print axioms Concurrency.RC11.hb_strength
#print axioms Concurrency.RC11.strength_sound
#print axioms Concurrency.RC11.raceFree_strength
#print axioms Concurrency.RC11.consistent_of_sc
#print axioms Concurrency.RC11.strength_sound_drf
#print axioms Concurrency.ClifMM.consistentF_of_sc
#print axioms Concurrency.Armv8.R_acyclic
#print axioms Concurrency.Mapping.Hom.psc_acyclic
#print axioms Concurrency.Mapping.armv8_to_clifF
#print axioms Concurrency.Mapping.plus_restr
-- the full aarch64.cat and LSE (T2g, #305)
#print axioms Concurrency.Armv8Full.consistent_frag
#print axioms Concurrency.Mapping.armv8full_to_clif
#print axioms Concurrency.Mapping.armv8full_to_clifF
#print axioms Concurrency.Lse.lse_maps
-- per-thread refinement with interference (T2h, #311, layer 0)
#print axioms Concurrency.ThreadRefine.Refines.trans
#print axioms Concurrency.ThreadRefine.realizes_of_threads
-- precise footprints, the VCode thread semantics (T2h, #311, layer 1)
#print axioms Concurrency.ArmInstFoot.footprint_exec_inst
#print axioms Concurrency.ArmInstFoot.footprint_stepi
#print axioms Concurrency.ArmInstFoot.kindsOk_stepEvs
#print axioms Concurrency.VCodeThread.ofoot_seq
#print axioms Concurrency.VCodeThread.sfoot_exec_inst
#print axioms Concurrency.VCodeThread.ofoot_execLines
#print axioms Concurrency.VCodeThread.ifoot_csem
#print axioms Concurrency.VCodeThread.vtstep_sc
#print axioms Concurrency.VCodeThread.exists_vtstep
#print axioms Concurrency.VCodeThread.Witness.stepEvs_ldaxr
#print axioms Concurrency.VCodeThread.Witness.cEvs_ldar
#print axioms Concurrency.VCodeThread.Witness.ldar_vtstep
-- event kinds, precise labels, private coherence, prepare, allocation, frame sets (T2h, #311)
#print axioms Concurrency.VCodeEvents.instEvs_kinds
#print axioms Concurrency.VCodeEvents.linesEvs_kinds
#print axioms Concurrency.VCodeEvents.cEvs_kinds
#print axioms Concurrency.VCodeEvents.cEvs_nil
#print axioms Concurrency.ArmPrecise.stepEvs_setMem
#print axioms Concurrency.ArmPrecise.exists_precise_step
#print axioms Concurrency.ArmPrecise.runs_of_P
#print axioms Concurrency.PrivCoh.privCoh_of_consistent
#print axioms Concurrency.PrivCoh.realizes_of_threads_priv
#print axioms Concurrency.PrivCoh.ownWrites_of_refines
#print axioms Concurrency.PrepThread.refines_of_thin
#print axioms Concurrency.PrepThread.prep_back
#print axioms Concurrency.PrepThread.prep_refines
#print axioms Concurrency.PrepThread.prep_refines_csem
#print axioms Concurrency.AllocThread.alloc_back
#print axioms Concurrency.AllocThread.alloc_refines
#print axioms Concurrency.FrameMono.csem_mono
#print axioms Concurrency.FrameMono.cEvs_mono
#print axioms Concurrency.FrameMono.vtrun_mono
#print axioms Concurrency.ThreadLayerWitness.instEvs_kinds_ldaxr
#print axioms Concurrency.ThreadLayerWitness.cEvs_kinds_ldar
#print axioms Concurrency.ThreadLayerWitness.cEvs_kinds_rmw
#print axioms Concurrency.ThreadLayerWitness.cEvs_nil_add
#print axioms Concurrency.ThreadLayerWitness.privCoh_own
#print axioms Concurrency.ThreadLayerWitness.privCoh_own_read
#print axioms Concurrency.ThreadLayerWitness.ret_threads_priv
#print axioms Concurrency.ThreadLayerWitness.ret_ownWrites
#print axioms Concurrency.ThreadLayerWitness.prep_ldar
#print axioms Concurrency.ThreadLayerWitness.alloc_ldar
#print axioms Concurrency.ThreadLayerWitness.precise_ldaxr
-- the Arm machine against the allocated code, run level (T2h, #311, layer 4b)
#print axioms Concurrency.ArmAllocThread.RefA.cons
#print axioms Concurrency.ArmAllocThread.RefA.refines
#print axioms Concurrency.ArmAllocThread.refines_of_itemSim
#print axioms Concurrency.ArmAllocThread.Witness.itemSim
#print axioms Concurrency.ArmAllocThread.Witness.refines_ldaxr
#print axioms Concurrency.ArmAllocThread.prun_own
#print axioms Concurrency.ArmAllocThread.prun_nil
#print axioms Concurrency.ArmAllocThread.prun_one_read
#print axioms Concurrency.ArmAllocThread.segEvs_execLines
#print axioms Concurrency.ArmAllocThread.step_execLines
#print axioms Concurrency.ArmAllocThread.nomem_execLines
#print axioms Concurrency.ArmAllocThread.q_patch
#print axioms Concurrency.ArmAllocThread.realizes_op_lines
#print axioms Concurrency.ArmAllocThread.itemSim_noev
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_noev
#print axioms Concurrency.ArmAllocThread.Witness.one_read_ldaxr
#print axioms Concurrency.ArmAllocThread.Witness.labelOffsets_one
#print axioms Concurrency.ArmAllocThread.Witness.wfN
#print axioms Concurrency.ArmAllocThread.Witness.qN
#print axioms Concurrency.ArmAllocThread.Witness.noev_premises
-- layer 4b, memory items (fence, ldar, stlr)
#print axioms Concurrency.ArmAllocThread.itemSim_of_op
#print axioms Concurrency.ArmAllocThread.noev_op
#print axioms Concurrency.ArmAllocThread.fence_op
#print axioms Concurrency.ArmAllocThread.ctlIndep_excl
#print axioms Concurrency.ArmAllocThread.straightSem_one
#print axioms Concurrency.ArmAllocThread.q_regs
#print axioms Concurrency.ArmAllocThread.oneEv_op
#print axioms Concurrency.ArmAllocThread.ldar_form
#print axioms Concurrency.ArmAllocThread.stlr_form
#print axioms Concurrency.ArmAllocThread.itemSim_mem
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_mem
#print axioms Concurrency.ArmAllocThread.exists_prun_line
#print axioms Concurrency.ArmAllocThread.MemWitness.mem_premises
#print axioms Concurrency.ArmAllocThread.MemWitness.dmb_run -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.MemWitness.dmb_refines -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.MemWitness.ldar_w
#print axioms Concurrency.ArmAllocThread.MemWitness.stlr_w
#print axioms Concurrency.ArmAllocThread.MemWitness.ctlIndep_ldar
-- the program level with fences and Rust orderings (T2f, #304)
#print axioms Concurrency.ProgE2E.rmw_sc
#print axioms Concurrency.ProgE2E.raceFreeProgF_of_raceFreeProg
#print axioms Concurrency.ProgE2E.raceFreeProgF_of_rust
#print axioms Concurrency.ProgE2E.consistentCF
#print axioms Concurrency.ProgE2E.program_correctF
#print axioms Concurrency.ProgE2E.program_correct_rust
#print axioms Concurrency.Witness.sbf_contract
#print axioms Concurrency.Witness.sbf_not_rc11
#print axioms Concurrency.Witness.mpf_consistentF
#print axioms Concurrency.Witness.mpf_rc11
#print axioms Concurrency.Witness.mpf_raceFree
#print axioms Concurrency.Witness.mpf_contract_raceFree
#print axioms Concurrency.Witness.incX_consistentF
-- non-vacuity witnesses
#print axioms Concurrency.ProgWitness.mp_replay
#print axioms Concurrency.ProgWitness.ret_raceFree
#print axioms Concurrency.ProgWitness.ret_correct
#print axioms Concurrency.ProgWitness.ret_rustRaceFree
#print axioms Concurrency.ProgWitness.ret_correctF
#print axioms Concurrency.ProgWitness.ret_correct_rust
#print axioms Concurrency.ProgWitness.ret_threads
#print axioms Concurrency.ProgWitness.ret_correct_threads
#print axioms Concurrency.ProgWitness.refines_spill
#print axioms Concurrency.ProgWitness.refines_trans_spill
#print axioms Concurrency.ArmThread.Witness.retry_run
#print axioms Concurrency.ArmThread.Witness.retry_succ
#print axioms Concurrency.ArmThread.Witness.evWrite_eq
#print axioms Concurrency.Witness.incX_premises
#print axioms Concurrency.Witness.incX_conclusions
#print axioms Concurrency.Witness.incX_interleaving
#print axioms Concurrency.Witness.mp_premises
#print axioms Concurrency.Witness.mp_sc
#print axioms Concurrency.Code.lines_kinds_witness
-- litmus tests (herd7 verdicts)
#print axioms Concurrency.Litmus.mp_rel_acq
#print axioms Concurrency.Litmus.mp_plain
#print axioms Concurrency.Litmus.mp_rel
#print axioms Concurrency.Litmus.mp_dmbs
#print axioms Concurrency.Litmus.sb_rel_acq
#print axioms Concurrency.Litmus.sb_plain
#print axioms Concurrency.Litmus.sb_dmbs
#print axioms Concurrency.Litmus.lb_acq_rel
#print axioms Concurrency.Litmus.lb_plain
#print axioms Concurrency.Litmus.w22_rels
#print axioms Concurrency.Litmus.w22_plain
#print axioms Concurrency.Litmus.iriw_acqs
#print axioms Concurrency.Litmus.iriw_plain
#print axioms Concurrency.Litmus.corr
#print axioms Concurrency.Litmus.corr_wf
#print axioms Concurrency.Litmus.inc_both0_a
#print axioms Concurrency.Litmus.inc_both0_b
#print axioms Concurrency.Litmus.inc_wf
#print axioms Concurrency.Litmus.inc_ok
#print axioms Concurrency.Litmus.gap_empty_wf
#print axioms Concurrency.Litmus.gap_fence_not_wf
#print axioms Concurrency.Exec.WfStrict.wf
#print axioms Concurrency.Armv8.atomicity
#print axioms Concurrency.Litmus.mp_full
#print axioms Concurrency.Litmus.mp_dmb_addr_frag
#print axioms Concurrency.Litmus.mp_dmb_addr_full
#print axioms Concurrency.Witness.incX_full
-- T2h layer 2a: VCode event addresses within the accesses
#print axioms Concurrency.VCodeAddr.load_lines_evs
#print axioms Concurrency.VCodeAddr.store_lines_evs
#print axioms Concurrency.VCodeAddr.fpuLoad_lines_evs
#print axioms Concurrency.VCodeAddr.fpuStore_lines_evs
#print axioms Concurrency.VCodeAddr.rmwBody_evs
#print axioms Concurrency.VCodeAddr.casHead_evs
#print axioms Concurrency.VCodeAddr.casStore_evs
#print axioms Concurrency.VCodeAddr.straightEvs_avoid
#print axioms Concurrency.VCodeAddr.cEvs_avoid
#print axioms Concurrency.VCodeAddr.Witness.ldar_avoid
-- T2h layer 2b: a segment run as a forward run
#print axioms Concurrency.SegRun.vtrun_patch
#print axioms Concurrency.SegRun.ldar_patch
-- T2h layer 2d core: accesses of a lowered statement by variation
#print axioms Concurrency.IselVary.store_touched
#print axioms Concurrency.IselVary.load_touched
-- T2h layer 2d: footprint lemma, CLIF facts, accesses within the run's events
#print axioms Concurrency.IselFoot.untouched_of_runOut
#print axioms Concurrency.IselFoot.store_in_events
#print axioms Concurrency.IselFoot.load_in_events
#print axioms Concurrency.IselClif.load_facts
#print axioms Concurrency.IselClif.store_facts
#print axioms Concurrency.IselClif.atomicLoad_facts
#print axioms Concurrency.IselClif.atomicStore_facts
#print axioms Concurrency.IselClif.atomicRmw_facts
#print axioms Concurrency.IselClif.atomicCas_facts
#print axioms Concurrency.IselClif.access_in_events
#print axioms Concurrency.IselClif.Witness.untouched_ldar
#print axioms Concurrency.IselClif.Witness.atomicLoad_facts0
#print axioms Concurrency.IselClif.Witness.store_facts0
-- T2h layer 2c: the shape of a statement's lowered code
#print axioms Concurrency.SegShape.segShape_segT
#print axioms Concurrency.SegShape.Witness.atomics_segShape -- witness: native_decide
-- T2h layer 2e groundwork: the CLIF thread steps of the memory statements
#print axioms Concurrency.ClifCStep.cstep_of_eval
#print axioms Concurrency.ClifCStep.cstep_load
#print axioms Concurrency.ClifCStep.cstep_store
#print axioms Concurrency.ClifCStep.cstep_atomicLoad
#print axioms Concurrency.ClifCStep.cstep_atomicStore
#print axioms Concurrency.ClifCStep.cstep_atomicRmw
#print axioms Concurrency.ClifCStep.cstep_atomicCas
#print axioms Concurrency.ClifCStep.cstep_fence
#print axioms Concurrency.ClifCStep.Witness.cstep_atomicLoad0
#print axioms Concurrency.ClifCStep.Witness.cstep_store0
#print axioms Concurrency.ClifCStep.Witness.cstep_atomicCas0
-- T2h layer 2d: from "touched" to the covering event, its address
#print axioms Concurrency.IselCover.cover_of_not_runOut
#print axioms Concurrency.IselCover.addr_eq_of_cover
#print axioms Concurrency.IselCover.Witness.cover_ldar
#print axioms Concurrency.IselCover.Witness.addr_eq_cover8
-- T2h layer 2e: the sizes of a VCode instruction's events
#print axioms Concurrency.VCodeSize.straightEvs_size
#print axioms Concurrency.VCodeSize.cEvs_size
#print axioms Concurrency.VCodeSize.addr_eq_of_oneAcc
#print axioms Concurrency.VCodeSize.Witness.ldar_oneAcc
#print axioms Concurrency.VCodeSize.Witness.ldar_at
-- T2h layer 2e: segment simulation pieces (footprints along a run, VCode determinism, counted LowerSim matches, CLIF steps without events, memory-statement helpers)
#print axioms Concurrency.SegFoot.csem_keep
#print axioms Concurrency.SegFoot.runFoot_csem
#print axioms Concurrency.SegFoot.Witness.keep_ldar
#print axioms Concurrency.SegFoot.Witness.seg_covered
#print axioms Concurrency.SegFoot.Witness.runFoot_ldar_fence
#print axioms Concurrency.SegFoot.Witness.fence_foot_after_ldar
#print axioms Concurrency.IselStep.vstep_det
#print axioms Concurrency.IselStep.vtrun_patchN
#print axioms Concurrency.IselStep.stmt_matchN
#print axioms Concurrency.IselStep.term_matchN
#print axioms Concurrency.IselSeg.vtrun_walk
#print axioms Concurrency.IselSeg.vtrun_follow
#print axioms Concurrency.IselSeg.mr_patch
#print axioms Concurrency.IselSeg.mr_own
#print axioms Concurrency.IselCheck.obligations_of_threadCheck
#print axioms Concurrency.CorrRefine.refines_of_corr
#print axioms Concurrency.ClifCStepTerm.done_of_step
#print axioms Concurrency.ClifCStepTerm.cstep_pure
#print axioms Concurrency.ClifCStepTerm.cstep_term
#print axioms Concurrency.IselThread.simRes_of_seg
#print axioms Concurrency.IselThread.pure_seg
#print axioms Concurrency.IselThread.term_seg
#print axioms Concurrency.IselMem.match_mem
#print axioms Concurrency.IselMem.vtstep_mem
#print axioms Concurrency.IselMemAux.cEvs_rmw_shape
#print axioms Concurrency.IselMemAux.cEvs_cas_shape
#print axioms Concurrency.IselMemAux.cEvs_fence
#print axioms Concurrency.IselMemAux.csem_keep_any
#print axioms Concurrency.IselMemAux.star_mem_keep
#print axioms Concurrency.IselMemAux.Witness.ldar_one_w0 -- witness: native_decide
#print axioms Concurrency.IselMemAux.Witness.fence_w0 -- witness: native_decide
#print axioms Concurrency.IselMemAux.Witness.rmw_shape_w0 -- witness: native_decide
#print axioms Concurrency.IselMemAux.Witness.cas_shape_w0 -- witness: native_decide
#print axioms Concurrency.IselMemAux.Witness.path1 -- witness: native_decide
#print axioms Concurrency.IselMemAux.Witness.star_rets -- witness: native_decide
#print axioms Concurrency.CEvsInv.cEvs_mapRegs
#print axioms Concurrency.CEvsInv.cEvs_setMem_common
#print axioms Concurrency.CEvsInv.cEvs_setMem_atA
#print axioms Concurrency.CEvsInv.Witness.ldar_atA_w0
#print axioms Concurrency.CEvsInv.Witness.ldar_renamed_atA
#print axioms Concurrency.IselVar.events_at_access
#print axioms Concurrency.IselMemSeg.mem_complete
#print axioms Concurrency.IselMemSeg.mem_split
#print axioms Concurrency.IselMemHelp.bytes_of_mr
#print axioms Concurrency.IselMemHelp.access_of_ok
#print axioms Concurrency.IselThread.Witness.driverHypA -- witness: native_decide
#print axioms Concurrency.IselMemLower.step_next_of
#print axioms Concurrency.IselMemLower.cas_cmp
#print axioms Concurrency.IselMemLower.mem_vreg
#print axioms Concurrency.IselMemMain.mem_seg
#print axioms Concurrency.IselRefines.seg_res
#print axioms Concurrency.IselRefines.isel_refines
#print axioms Concurrency.IselRefines.Witness.isel_refines_fA -- witness: native_decide
#print axioms Concurrency.IselEntry.entry_matchN
#print axioms Concurrency.IselEntry.entryLoads_nil
#print axioms Concurrency.IselEntry.isel_refines_entry
#print axioms Concurrency.IselRefines.Witness.isel_refines_entry_fA -- witness: native_decide
#print axioms Concurrency.PrepThread.prep_thin
#print axioms Concurrency.PrepThread.prep_thin_csem
#print axioms Concurrency.AllocThread.alloc_thin
#print axioms Concurrency.ThreadCompose.Thin.trans
#print axioms Concurrency.ThreadCompose.Thin.take
#print axioms Concurrency.ThreadCompose.Refines.congr
#print axioms Concurrency.ThreadCompose.Refines.take
#print axioms Concurrency.ThreadCompose.isel_alloc_refines
#print axioms Concurrency.ThreadCompose.prun_len
#print axioms Concurrency.ThreadCompose.csemV_none
#print axioms Concurrency.ThreadCompose.arm_isel_refines
#print axioms Concurrency.ThreadCompose.Witness.thin_take_w
#print axioms Concurrency.ThreadCompose.Witness.refines_take_w
#print axioms Concurrency.ThreadCompose.Witness.isel_alloc_refines_fA -- witness: native_decide
-- T2k (#311): layer 4b with moves, arm_isel_refinesE, Realizes for compiled code
#print axioms Backend.Proof.moveLines_evs
#print axioms Backend.Proof.moveLines_noStx
#print axioms Concurrency.ArmAllocThread.moveCodeOk
#print axioms Concurrency.ArmAllocThread.prun_priv
#print axioms Concurrency.ArmAllocThread.move_op
#print axioms Concurrency.ArmAllocThread.itemSim_of_op_ok
#print axioms Concurrency.ArmAllocThread.itemSim_mv
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_mv
#print axioms Concurrency.ThreadCompose.arm_isel_refinesE
#print axioms Concurrency.RealizeCompiled.crun_states
#print axioms Concurrency.RealizeCompiled.Refines.pairT_congr
#print axioms Concurrency.RealizeCompiled.monPair_take
#print axioms Concurrency.RealizeCompiled.thread_compiled
#print axioms Concurrency.RealizeCompiled.realizes_compiled
#print axioms Concurrency.RealizeCompiled.wf_noReads
#print axioms Concurrency.RealizeCompiled.Witness.driverHyp_of
#print axioms Concurrency.RealizeCompiled.Witness.compiledF -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.Witness.mv_premises -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.Witness.realizes_nil -- witness: native_decide
-- T2h (#311): layer 4b for the plain load/store items (CtlIndep of the encoded forms)
#print axioms Concurrency.ArmAllocThread.sameCtl_gpr_load
#print axioms Concurrency.ArmAllocThread.sameCtl_gpr_load_err
#print axioms Concurrency.ArmAllocThread.sameCtl_gpr_store
#print axioms Concurrency.ArmAllocThread.sameCtl_gpr_store_err
#print axioms Concurrency.ArmAllocThread.sameCtl_fp_load
#print axioms Concurrency.ArmAllocThread.sameCtl_fp_load_err
#print axioms Concurrency.ArmAllocThread.sameCtl_fp_store
#print axioms Concurrency.ArmAllocThread.sameCtl_fp_store_err
#print axioms Concurrency.ArmAllocThread.sameCtl_ldstur_load
#print axioms Concurrency.ArmAllocThread.sameCtl_ldstur_load_err
#print axioms Concurrency.ArmAllocThread.sameCtl_ldstur_store
#print axioms Concurrency.ArmAllocThread.sameCtl_ldstur_store_err
#print axioms Concurrency.ArmAllocThread.ctlIndep_uimm_load
#print axioms Concurrency.ArmAllocThread.ctlIndep_uimm_store
#print axioms Concurrency.ArmAllocThread.ctlIndep_unsc_load
#print axioms Concurrency.ArmAllocThread.ctlIndep_unsc_store
#print axioms Concurrency.ArmAllocThread.ctlIndep_reg_load
#print axioms Concurrency.ArmAllocThread.ctlIndep_reg_store
#print axioms Concurrency.ArmAllocThread.ctlIndep_fpUimm_load
#print axioms Concurrency.ArmAllocThread.ctlIndep_fpUimm_store
#print axioms Concurrency.ArmAllocThread.ctlIndep_fpReg_load
#print axioms Concurrency.ArmAllocThread.ctlIndep_fpReg_store
#print axioms Concurrency.ArmAllocThread.ctlIndep_fpUnsc_load
#print axioms Concurrency.ArmAllocThread.ctlIndep_fpUnsc_store
#print axioms Concurrency.ArmAllocThread.linesEvs_insKind_none
#print axioms Concurrency.ArmAllocThread.preMem
#print axioms Concurrency.ArmAllocThread.straightSem_pre
#print axioms Concurrency.ArmAllocThread.immEvs_load_eq
#print axioms Concurrency.ArmAllocThread.immEvs_store_eq
-- T2k (#311): forward precise runs, realizes_fence
#print axioms Concurrency.ArmAllocThread.move_lines
#print axioms Concurrency.ArmAllocThread.step_fwd
#print axioms Concurrency.ArmAllocThread.prun_fwd
#print axioms Concurrency.ArmAllocThread.move_fwd
#print axioms Concurrency.ArmAllocThread.moves_fwd
#print axioms Concurrency.ArmAllocThread.q_head
#print axioms Concurrency.RealizeCompiled.Witness.compiled_of -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.Witness.realizes_fence -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.wf_single
#print axioms Concurrency.RealizeCompiled.wf_single_witness

-- T2 (#311): layer 4b for the LL/SC loops (retries, monitor pairs)
#print axioms Concurrency.ArmAllocThread.noW_append
#print axioms Concurrency.ArmAllocThread.retryOut_shift
#print axioms Concurrency.ArmAllocThread.retry_run
#print axioms Concurrency.ArmAllocThread.evAt_seg
#print axioms Concurrency.ArmAllocThread.img_pair
#print axioms Concurrency.ArmAllocThread.img_one
#print axioms Concurrency.ArmLoop.rmwBody_keepFlags
#print axioms Concurrency.ArmLoop.rmwBody_dep
#print axioms Concurrency.ArmLoop.rmwBody_evsEq
#print axioms Concurrency.ArmLoop.casHead_dep
#print axioms Concurrency.ArmLoop.casStore_evsEq
#print axioms Concurrency.ArmLoop.ldaxr_cls
#print axioms Concurrency.ArmLoop.stlxr_cls
#print axioms Concurrency.ArmLoop.stlxr_frame
#print axioms Concurrency.ArmAllocThread.writeM_writeM
#print axioms Concurrency.ArmAllocThread.r_failState
#print axioms Concurrency.ArmAllocThread.execLines_mem_of_R
#print axioms Concurrency.ArmAllocThread.rmw_steps
#print axioms Concurrency.ArmAllocThread.rmw_retry
#print axioms Concurrency.ArmAllocThread.rmw_op
#print axioms Concurrency.ArmAllocThread.cas_steps
#print axioms Concurrency.ArmAllocThread.cas_retry
#print axioms Concurrency.ArmAllocThread.cas_op
#print axioms Concurrency.ArmAllocThread.itemSim_loop
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_loop
#print axioms Concurrency.ArmAllocThread.LoopWitness.not_noMoves
#print axioms Concurrency.ArmAllocThread.LoopWitness.loop_premises -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.LoopWitness.rmw_retry_w -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.LoopWitness.cas_retry_w -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.LoopWitness.retry_run_w -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.moves_fwdA
#print axioms Concurrency.ArmAllocThread.excl_step_fwd
#print axioms Concurrency.ArmAllocThread.codeLinesE_head_ldar
#print axioms Concurrency.ArmAllocThread.codeLinesE_head_stlr
#print axioms Concurrency.RealizeCompiled.WitnessL.realizes_one
#print axioms Concurrency.RealizeCompiled.WitnessL.compiled_ofL -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessL.realizes_load -- witness: native_decide

-- T2 (#311): layer 4b for the block-ending branches (block-rank measure, fall-through jumps)
#print axioms Concurrency.ArmAllocThread.br_noEv
#print axioms Concurrency.ArmAllocThread.reach_bE
#print axioms Concurrency.ArmAllocThread.reach_rcbE
#print axioms Concurrency.ArmAllocThread.reach_cbE
#print axioms Concurrency.ArmAllocThread.labelOffsets_go_nodup
#print axioms Concurrency.ArmAllocThread.af_nodup
#print axioms Concurrency.ArmAllocThread.succ_of_label
#print axioms Concurrency.ArmAllocThread.head_label
#print axioms Concurrency.ArmAllocThread.μR_succ
#print axioms Concurrency.ArmAllocThread.μR_lt
#print axioms Concurrency.ArmAllocThread.csem_goto
#print axioms Concurrency.ArmAllocThread.realizes_gotoE
#print axioms Concurrency.ArmAllocThread.goto_op
#print axioms Concurrency.ArmAllocThread.sameB_step
#print axioms Concurrency.ArmAllocThread.opOutR_of
#print axioms Concurrency.ArmAllocThread.opOut_okPriv
#print axioms Concurrency.ArmAllocThread.memScopeB_of_memScopeL
#print axioms Concurrency.ArmAllocThread.itemSim_br
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_br
#print axioms Concurrency.ArmAllocThread.BranchWitness.scopeB
#print axioms Concurrency.ArmAllocThread.BranchWitness.not_memScopeL
#print axioms Concurrency.ArmAllocThread.BranchWitness.jump_dropped -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.BranchWitness.br_premises -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.Witness.wf_ofAt
#print axioms Concurrency.ArmAllocThread.Witness.abi_ofAt
#print axioms Concurrency.RealizeCompiled.WitnessS.compiled_ofS -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessS.realizes_store -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.wf_multi
#print axioms Concurrency.ArmAllocThread.moves_fwdA
#print axioms Concurrency.RealizeCompiled.WitnessL.run_load -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessS.run_store -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessMP.realizes_n
#print axioms Concurrency.RealizeCompiled.WitnessMP.fB_iv
#print axioms Concurrency.RealizeCompiled.WitnessMP.priv_disj -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessMP.realizes_mp -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessMP.mp_reads -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.Compiled.toB
#print axioms Concurrency.RealizeCompiled.thread_compiledB
#print axioms Concurrency.RealizeCompiled.realizes_compiledB
#print axioms Concurrency.RealizeCompiled.CompiledB.toLS
#print axioms Concurrency.RealizeCompiled.thread_compiledLS
#print axioms Concurrency.RealizeCompiled.realizes_compiledLS
#print axioms Concurrency.ArmAllocThread.exists_prun_lineS
#print axioms Concurrency.ArmAllocThread.step_fwdS
#print axioms Concurrency.ArmAllocThread.prun_quiet
#print axioms Concurrency.ArmAllocThread.rmw_at
#print axioms Concurrency.ArmAllocThread.rmw_fwd
#print axioms Concurrency.ArmAllocThread.rmw_lines

-- T2 (#311): layer 4b calls, the linking induction (callee events through the callee's refinement)
#print axioms Concurrency.CallCompose.XClosed.append
#print axioms Concurrency.CallCompose.monPair_left
#print axioms Concurrency.CallCompose.monPair_right
#print axioms Concurrency.CallCompose.Refines.app
#print axioms Concurrency.CallCompose.Realized.trans
#print axioms Concurrency.CallCompose.ExtEvContract.funReal
#print axioms Concurrency.CallCompose.link_compose
#print axioms Concurrency.CallCompose.link_compose_ext
#print axioms Concurrency.CallCompose.realizes_linked
#print axioms Concurrency.CallCompose.Witness.prun_sE
#print axioms Concurrency.CallCompose.Witness.realized_noev
#print axioms Concurrency.CallCompose.Witness.segOk_caller
#print axioms Concurrency.CallCompose.Witness.extContract
#print axioms Concurrency.CallCompose.Witness.linked_sE
-- T2h (#311): layer 4b with the plain loads/stores (ArmAllocLS)
#print axioms Concurrency.ArmAllocThread.immEvs_load_cf
#print axioms Concurrency.ArmAllocThread.immEvs_store_cf
#print axioms Concurrency.ArmAllocThread.load_line_shape
#print axioms Concurrency.ArmAllocThread.store_line_shape
#print axioms Concurrency.ArmAllocThread.allp_nil
#print axioms Concurrency.ArmAllocThread.allp_ite
#print axioms Concurrency.ArmAllocThread.allp_one
#print axioms Concurrency.ArmAllocThread.shl8_pos
#print axioms Concurrency.ArmAllocThread.p_immEvs
#print axioms Concurrency.ArmAllocThread.p_ldsturEvs
#print axioms Concurrency.ArmAllocThread.ldstFields_plain
#print axioms Concurrency.ArmAllocThread.ldstFields_bind_plain
#print axioms Concurrency.ArmAllocThread.ldstFields_bind2_plain
#print axioms Concurrency.ArmAllocThread.plain_arm
#print axioms Concurrency.ArmAllocThread.load_line_cf
#print axioms Concurrency.ArmAllocThread.store_line_cf
#print axioms Concurrency.ArmAllocThread.bindE_ok
#print axioms Concurrency.ArmAllocThread.encSP_v
#print axioms Concurrency.ArmAllocThread.encZR_v
#print axioms Concurrency.ArmAllocThread.immEvs_fpLoad_cf
#print axioms Concurrency.ArmAllocThread.ldsturEvs_fpLoad_cf
#print axioms Concurrency.ArmAllocThread.immEvs_fpStore_cf
#print axioms Concurrency.ArmAllocThread.ldsturEvs_fpStore_cf
#print axioms Concurrency.ArmAllocThread.fpuLoad_line_cf
#print axioms Concurrency.ArmAllocThread.fpuStore_line_cf
#print axioms Concurrency.ArmAllocThread.x_or_v
#print axioms Concurrency.ArmAllocThread.v_or_x
#print axioms Concurrency.ArmAllocThread.load_uoff_form
#print axioms Concurrency.ArmAllocThread.load_unsc_form
#print axioms Concurrency.ArmAllocThread.load_regReg_form
#print axioms Concurrency.ArmAllocThread.load_regScaled_form
#print axioms Concurrency.ArmAllocThread.load_regScaledExt_form
#print axioms Concurrency.ArmAllocThread.load_regExt_form
#print axioms Concurrency.ArmAllocThread.store_uoff_form
#print axioms Concurrency.ArmAllocThread.store_unsc_form
#print axioms Concurrency.ArmAllocThread.store_regReg_form
#print axioms Concurrency.ArmAllocThread.store_regScaled_form
#print axioms Concurrency.ArmAllocThread.store_regScaledExt_form
#print axioms Concurrency.ArmAllocThread.store_regExt_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_uoff_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_unsc_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_regReg_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_regScaled_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_regScaledExt_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_regExt_form
#print axioms Concurrency.ArmAllocThread.fpuStore_uoff_form
#print axioms Concurrency.ArmAllocThread.fpuStore_unsc_form
#print axioms Concurrency.ArmAllocThread.fpuStore_regReg_form
#print axioms Concurrency.ArmAllocThread.fpuStore_regScaled_form
#print axioms Concurrency.ArmAllocThread.fpuStore_regScaledExt_form
#print axioms Concurrency.ArmAllocThread.fpuStore_regExt_form
#print axioms Concurrency.ArmAllocThread.load_lsForm
#print axioms Concurrency.ArmAllocThread.store_lsForm
#print axioms Concurrency.ArmAllocThread.fpuLoad_lsForm
#print axioms Concurrency.ArmAllocThread.fpuStore_lsForm
#print axioms Concurrency.ArmAllocThread.lsForm_oneEv
#print axioms Concurrency.ArmAllocThread.noGoto_ls
#print axioms Concurrency.ArmAllocThread.memScopeLS_of_memScopeB
#print axioms Concurrency.ArmAllocThread.itemSim_ls
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_ls
#print axioms Concurrency.ArmAllocThread.LSWitness.wfS -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.LSWitness.scopeS
#print axioms Concurrency.ArmAllocThread.LSWitness.not_memScopeB
#print axioms Concurrency.ArmAllocThread.LSWitness.ls_premises -- witness: native_decide

-- T2 (#311): layer 4b from the ABI entry (the prologue)
#print axioms Concurrency.ArmAllocThread.stp_fplr_evs
#print axioms Concurrency.ArmAllocThread.q_init_lines
#print axioms Concurrency.ArmAllocThread.prologue_evs
#print axioms Concurrency.ArmAllocThread.prun_prologue
#print axioms Concurrency.ArmAllocThread.refines_privW
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_entry
#print axioms Concurrency.RealizeCompiled.WitnessL.entry_premises -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessL.run_load_entry -- witness: native_decide
#print axioms Concurrency.RealizeCompiled.WitnessL.refines_load_entry -- witness: native_decide
#print axioms Concurrency.ArmAllocThread.immEvs_unal
#print axioms Concurrency.ArmAllocThread.ldsturEvs_unal
#print axioms Concurrency.ArmAllocThread.ldst_unal
#print axioms Concurrency.ArmAllocThread.stackFin
#print axioms Concurrency.ArmAllocThread.regs1
#print axioms Concurrency.ArmAllocThread.s16_align
#print axioms Concurrency.ArmAllocThread.regX_stack
#print axioms Concurrency.ArmAllocThread.load_stack_form
#print axioms Concurrency.ArmAllocThread.store_stack_form
#print axioms Concurrency.ArmAllocThread.fpuLoad_stack_form
#print axioms Concurrency.ArmAllocThread.fpuStore_stack_form
#print axioms Concurrency.ArmAllocThread.load_lsFinal
#print axioms Concurrency.ArmAllocThread.store_lsFinal
#print axioms Concurrency.ArmAllocThread.fpuLoad_lsFinal
#print axioms Concurrency.ArmAllocThread.fpuStore_lsFinal

-- T2 (#311): calls — the thread from the ABI entry, CLIF callers-lifting, the callee contract
#print axioms Concurrency.ThreadCompose.arm_isel_refinesE'
#print axioms Concurrency.ArmAllocThread.prologue_linesAt
#print axioms Concurrency.ArmAllocThread.arm_alloc_refines_entryQ
#print axioms Concurrency.ArmFoot.exec_inst_program
#print axioms Concurrency.ArmFoot.stepi_program
#print axioms Concurrency.ClifLift.step_pushC
#print axioms Concurrency.ClifLift.cstep_pushC
#print axioms Concurrency.ClifLift.cstep_ret_nil
#print axioms Concurrency.ClifLift.crun_pushC
#print axioms Concurrency.CallThread.thread_compiled_entry
#print axioms Concurrency.CallThread.refines_prefix_nil
#print axioms Concurrency.CallThread.prun_transfer
#print axioms Concurrency.CallThread.xClosed_noStx
#print axioms Concurrency.CallThread.xClosed_runs
#print axioms Concurrency.CallThread.funReal_callee
#print axioms Concurrency.CallThread.Witness.compiledE_L -- witness: native_decide
#print axioms Concurrency.CallThread.Witness.thread_load_entry -- witness: native_decide
#print axioms Concurrency.CallThread.Witness.armStepX_program
#print axioms Concurrency.CallThread.Witness.noStxL -- witness: native_decide
#print axioms Concurrency.CallThread.Witness.funReal_load -- witness: native_decide
