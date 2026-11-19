import FV.Opt.Proof.MidValMem
import FV.Opt.Proof.MidValMemWitness
import FV.Opt.Proof.SemSimMU
import FV.Opt.Proof.SemSimMWitness
import FV.Opt.Proof.MidValProg
import FV.Opt.Proof.MidValNeg
import FVTest.Opt.MidValWitness
import FVTest.Opt.MidValNegWitness
import FVTest.Opt.MidValGapWitness
import FVTest.Opt.MidValNormWitness
import FVTest.Opt.MidValAlgWitness

-- #1119 (c) stage 1: the memory facts of the mid-end validator `Opt.MidVal.check`
#print axioms Clif.Mem.readFold_spec
#print axioms Clif.Mem.readFold_some
#print axioms Clif.Mem.writeBits_bytes
#print axioms Clif.Mem.readBits_writeBits
#print axioms Clif.Mem.checkAccess_ok_valid
#print axioms Clif.Mem.checkAccess_of_valid
#print axioms Clif.Mem.load_of_store
#print axioms Clif.Mem.load_of_load
#print axioms Clif.Mem.MidValWitness.store_ok
#print axioms Clif.Mem.MidValWitness.store_ok_big
#print axioms Clif.Mem.MidValWitness.fwd_lemma
#print axioms Clif.Mem.MidValWitness.fwd_big_lemma
#print axioms Clif.Mem.MidValWitness.fwd
#print axioms Clif.Mem.MidValWitness.fwd_big
#print axioms Clif.Mem.MidValWitness.rle_lemma
#print axioms Clif.Mem.MidValWitness.rle

-- (3) the memory-aware simulation `FunSimMU` and its program-level lifting
#print axioms Opt.IsSimM.star
#print axioms Opt.ContM.comp
#print axioms Opt.ContM.mono
#print axioms Opt.IsSimM.comp
#print axioms Opt.TryOkMU.toTryOkM
#print axioms Opt.TContM.comp
#print axioms Opt.TContM.mono
#print axioms Opt.HContM.comp
#print axioms Opt.HContM.mono
#print axioms Opt.IsSimMU.comp
#print axioms Opt.Cont.toM
#print axioms Opt.TCont.toM
#print axioms Opt.HCont.toM
#print axioms Opt.IsSimU.toMU
#print axioms Opt.FunSimU.toMU
#print axioms Opt.FunSimMU.refl
#print axioms Opt.FunSimMU.trans
#print axioms Opt.FunsSimMU.map
#print axioms Opt.FunsSimU.toMU
#print axioms Opt.FunsSimMU.findP
#print axioms Opt.FunsSimMU.externNames
#print axioms Opt.GRMU.of
#print axioms Opt.TContM.toContMU
#print axioms Opt.TabRelM.none'
#print axioms Opt.TabRelM.ofH
#print axioms Opt.TabRelM.bt
#print axioms Opt.CallersRelMU.length
#print axioms Opt.GRU.toMU
#print axioms Opt.TabRel.toM
#print axioms Opt.CallersRelU.toMU
#print axioms Opt.SRU.toMU
#print axioms Opt.XStepRelMU.stuck'
#print axioms Opt.XStepRelMU.trapped'
#print axioms Opt.XStepRelMU.done'
#print axioms Opt.XStepRelMU.same'
#print axioms Opt.XStepRelMU.push'
#print axioms Opt.XStepRelMU.pop'
#print axioms Opt.funSimMU_entry
#print axioms Opt.returnValues_relMU
#print axioms Opt.callCont_relMU
#print axioms Opt.tailCont_relMU
#print axioms Opt.ciCont_relMU
#print axioms Opt.sim_step_lstepMU
#print axioms Opt.sim_stepMU_core
#print axioms Opt.extRaise_congrMU
#print axioms Opt.indRaise_congrMU
#print axioms Opt.unwindFrom_relMU
#print axioms Opt.raiseIn_relMU
#print axioms Opt.sim_raiseMU
#print axioms Opt.XStepRelMU.toStepX
#print axioms Opt.sim_stepMU
#print axioms Opt.runLoopX_refinesSRMU
#print axioms Opt.runLoopX_refinesMU
-- (3) at one symbol table (#1119 follow-up: the hoisting mode)
#print axioms Opt.FunSimMU.at
#print axioms Opt.FunSimMUAt.trans
#print axioms Opt.FunsSimMU.at
#print axioms Opt.FunsSimMUAt.findP
#print axioms Opt.FunsSimMUAt.externNames
#print axioms Opt.funSimMUAt_entry
#print axioms Opt.callCont_relMUAt
#print axioms Opt.tailCont_relMUAt
#print axioms Opt.ciCont_relMUAt
#print axioms Opt.sim_step_lstepMUAt
#print axioms Opt.sim_stepMU_coreAt
#print axioms Opt.extRaise_congrMUAt
#print axioms Opt.indRaise_congrMUAt
#print axioms Opt.sim_raiseMUAt
#print axioms Opt.sim_stepMUAt
#print axioms Opt.runLoopX_refinesSRMUAt
#print axioms Opt.runLoopX_refinesMUAt
-- (3) witnesses (native_decide of ConstPhiWitness only)
#print axioms Opt.SemSimMWitness.fwd_simMU -- witness: native_decide
#print axioms Opt.SemSimMWitness.fwd_simMU_trans -- witness: native_decide
#print axioms Opt.SemSimMWitness.pq_simMU -- witness: native_decide
#print axioms Opt.SemSimMWitness.entry_sru -- witness: native_decide
#print axioms Opt.SemSimMWitness.fwd_refinesMU -- witness: native_decide
#print axioms Opt.SemSimMWitness.p_returns
#print axioms Opt.SemSimMWitness.q_returns -- witness: native_decide
-- (4) the facts of `wfCheck` (#1119 follow-up: `call_indirect` result types, `bitcast` typing)
#print axioms Opt.MidVal.wfCertM_sound
#print axioms Opt.MidVal.wfM_of_wfCheck
#print axioms Opt.MidVal.WfM.site_result
#print axioms Opt.MidVal.WfM.site_param
#print axioms Opt.MidVal.WfM.site_stmt
#print axioms Opt.MidVal.WfM.site_param'
#print axioms Opt.MidVal.WfM.site_bound
#print axioms Opt.MidVal.WfM.avail_operand
#print axioms Opt.MidVal.WfM.avail_not_result
#print axioms Opt.MidVal.WfM.avail_succ
#print axioms Opt.MidVal.WfM.avail_entry
#print axioms Opt.MidVal.WfM.idx_unique
#print axioms Opt.MidVal.WfM.avail_pred
#print axioms Opt.MidVal.WfM.block?_index
#print axioms Opt.MidVal.WfM.avail_lt
#print axioms Opt.MidVal.WfM.inv_results
#print axioms Opt.MidVal.WfM.inv_entry
#print axioms Opt.MidVal.WfM.inv_enter
#print axioms Opt.MidVal.WfM.inv_regs_congr
-- (5) MidValTerm
#print axioms Opt.MidVal.CC.le_sound
#print axioms Opt.MidVal.LeP.trans
#print axioms Opt.MidVal.atomVal_defSite
#print axioms Opt.MidVal.CC.tmOk_atom
#print axioms Opt.MidVal.CC.tmOk_node
#print axioms Opt.MidVal.CC.tmsOk_get
#print axioms Opt.MidVal.tmVal_eq
#print axioms Opt.MidVal.tmVal_atom
#print axioms Opt.MidVal.tmVal_node
#print axioms Opt.MidVal.tmVal_mapOperands
#print axioms Opt.MidVal.tmVal_mapOperands_inst
#print axioms Opt.MidVal.tmVal_congr_of
#print axioms Opt.MidVal.tmVal_congr
#print axioms Opt.MidVal.normSound_id
-- (5) MidValSpec
#print axioms Opt.MidVal.sameHeader_spec
#print axioms Opt.MidVal.CC.blocksOk_spec
#print axioms Opt.MidVal.checkCertWith_spec
#print axioms Opt.MidVal.checkCert_spec
-- (5) MidValWalk
#print axioms Opt.MidVal.pureOk_spec
#print axioms Opt.MidVal.resOk_spec
#print axioms Opt.MidVal.gPre_spec
#print axioms Opt.MidVal.nextSkel_append
#print axioms Opt.MidVal.nextSkel_skelHead
#print axioms Opt.MidVal.GPreStmt.nopOrPure
#print axioms Opt.MidVal.walk_nil_spec
#print axioms Opt.MidVal.walk_nop
#print axioms Opt.MidVal.walk_pure_spec
#print axioms Opt.MidVal.walk_skel_spec
#print axioms Opt.MidVal.removeOk_spec
#print axioms Opt.MidVal.blockOk_spec
#print axioms Opt.MidVal.entryOk_spec
-- (5) MidValFacts
#print axioms Opt.MidVal.loadKind_inj
#print axioms Opt.MidVal.loadKind_eq_storeKind
#print axioms Opt.MidVal.setWidth_loadExt
#print axioms Opt.MidVal.loadExt_setWidth_loadExt
#print axioms Opt.MidVal.loadExt_load
#print axioms Opt.MidVal.memHolds_congr
#print axioms Opt.MidVal.memHolds_of_eq
#print axioms Opt.MidVal.memHolds_unique
#print axioms Opt.MidVal.writeBits_self
#print axioms Opt.MidVal.evalInst_load_of_holds
#print axioms Opt.MidVal.holds_of_evalInst_load
#print axioms Opt.MidVal.evalInst_load_notrap
#print axioms Opt.MidVal.holds_of_evalInst_store
#print axioms Opt.MidVal.evalInst_store_idem
#print axioms Opt.MidVal.evalInst_mergeK_eq
#print axioms Opt.MidVal.evalInst_mergeK
-- (5) MidValFloat
#print axioms Opt.MidVal.getMany_typed
#print axioms Opt.MidVal.evalFloat_total
#print axioms Opt.MidVal.evalInst_float_total
#print axioms Opt.MidVal.evalInst_pureK_totalM
#print axioms Opt.MidVal.evalInst_pureK_total
#print axioms Opt.MidVal.pureK_not_call
#print axioms Opt.MidVal.pureK_mem
#print axioms Opt.MidVal.evalInst_pureK_mem
#print axioms Opt.MidVal.evalNode_pureK_mem
#print axioms Opt.MidVal.evalInst_pureK_ok_mem
-- (5) MidValRel
#print axioms Opt.MidVal.Hyp.wff
#print axioms Opt.MidVal.Hyp.wfg
#print axioms Opt.MidVal.Hyp.idomF
#print axioms Opt.MidVal.Hyp.idomG
#print axioms Opt.MidVal.Hyp.idomC
#print axioms Opt.MidVal.Hyp.rankF
#print axioms Opt.MidVal.Hyp.le_sound
#print axioms Opt.MidVal.Hyp.leP_trans
#print axioms Opt.MidVal.Hyp.siteF
#print axioms Opt.MidVal.Hyp.TV_stable
#print axioms Opt.MidVal.FactHolds.stable
-- (5) MidValEntry
#print axioms Opt.MidVal.param_index
#print axioms Opt.MidVal.tv_param
#print axioms Opt.MidVal.entry_param
#print axioms Opt.MidVal.entry_paramM
#print axioms Opt.MidVal.evalInst_partial_resolves
#print axioms Opt.MidVal.entry_facts_hold
#print axioms Opt.MidVal.rel_entry
-- (5) MidValPrefix
#print axioms Opt.MidVal.evalNode_pureK_syms
#print axioms Opt.MidVal.evalInst_of_evalNode
#print axioms Opt.MidVal.avail_succ
#print axioms Opt.MidVal.results_len
#print axioms Opt.MidVal.gStep
#print axioms Opt.MidVal.gStmt
#print axioms Opt.MidVal.gPre_run_list
#print axioms Opt.MidVal.gPre_run
-- (5) MidValFStep
#print axioms Opt.MidVal.FStep.evalNode_of_ok
#print axioms Opt.MidVal.FStep.evalNode_pureK_syms
#print axioms Opt.MidVal.FStep.partialK_notrap
#print axioms Opt.MidVal.FStep.evalInst_partialK
#print axioms Opt.MidVal.FStep.mapOperands_eq_load
#print axioms Opt.MidVal.FStep.mapOperands_eq_store
#print axioms Opt.MidVal.FStep.mergeK_mapOperands
#print axioms Opt.MidVal.FStep.isPure_of_mergeK
#print axioms Opt.MidVal.FStep.notCall_of_mergeK
#print axioms Opt.MidVal.FStep.setMany_single
#print axioms Opt.MidVal.FStep.stmt_at
#print axioms Opt.MidVal.FStep.walk_frames
#print axioms Opt.MidVal.FStep.regs_after
#print axioms Opt.MidVal.FStep.TV_after
#print axioms Opt.MidVal.FStep.rel_after
#print axioms Opt.MidVal.FStep.TV_pureOk
#print axioms Opt.MidVal.rel_nop
#print axioms Opt.MidVal.rel_pure
#print axioms Opt.MidVal.rel_remove
-- (5) MidValMatch
#print axioms Opt.MidVal.mapOperands_eq_call
#print axioms Opt.MidVal.not_call_of_mapOperands
#print axioms Opt.MidVal.mergeK_mapOperands
#print axioms Opt.MidVal.writerK_mapOperands
#print axioms Opt.MidVal.isPure_of_pureK
#print axioms Opt.MidVal.resultTypes_mergeK_len
#print axioms Opt.MidVal.evalInst_mem_of_not_writer
#print axioms Opt.MidVal.mem_afterKeep
#print axioms Opt.MidVal.memFact?_mapOperands
#print axioms Opt.MidVal.resVal
#print axioms Opt.MidVal.TV_res
#print axioms Opt.MidVal.mapOperands_eq_callIndirect
#print axioms Opt.MidVal.ciArgs_ren
#print axioms Opt.MidVal.no_callIndirect
#print axioms Opt.MidVal.callArgs_ren
#print axioms Opt.MidVal.matched_ctx
#print axioms Opt.MidVal.MCtx.eval
#print axioms Opt.MidVal.MCtx.call
#print axioms Opt.MidVal.rel_bind
#print axioms Opt.MidVal.facts_next
#print axioms Opt.MidVal.matched_next
#print axioms Opt.MidVal.matched_trap
#print axioms Opt.MidVal.matched_ci
#print axioms Opt.MidVal.matched_call
#print axioms Opt.MidVal.rel_matched
-- (5) MidValTermin
#print axioms Opt.MidVal.Tn.inv_end
#print axioms Opt.MidVal.Tn.inB_of_inv
#print axioms Opt.MidVal.Tn.pw2_of_map
#print axioms Opt.MidVal.Tn.getMany_norm
#print axioms Opt.MidVal.Tn.tailArgs_pw
#print axioms Opt.MidVal.Tn.callArgs_pw
#print axioms Opt.MidVal.Tn.ciArgs_pw
#print axioms Opt.MidVal.Tn.sel_pair
#print axioms Opt.MidVal.Tn.mapVals_args
#print axioms Opt.MidVal.Tn.val_mem_vals
#print axioms Opt.MidVal.Tn.resolve_pair2
#print axioms Opt.MidVal.Tn.resolveH_pair2
#print axioms Opt.MidVal.Tn.tryNormal_pair2
#print axioms Opt.MidVal.Tn.tryHandler_pair2
#print axioms Opt.MidVal.Tn.setMany_param
#print axioms Opt.MidVal.Tn.params_uniq
#print axioms Opt.MidVal.Tn.set_lo
#print axioms Opt.MidVal.Tn.win_set
#print axioms Opt.MidVal.Tn.win_enter
#print axioms Opt.MidVal.Tn.nomem
#print axioms Opt.MidVal.Tn.term_step
#print axioms Opt.MidVal.Tn.id_eq
#print axioms Opt.MidVal.Tn.block?_g
#print axioms Opt.MidVal.Tn.strict_of_le
#print axioms Opt.MidVal.Tn.strict_of_anc
#print axioms Opt.MidVal.Tn.TV_closed
#print axioms Opt.MidVal.Tn.TV_enter
#print axioms Opt.MidVal.Tn.tv_param
#print axioms Opt.MidVal.Tn.factHolds_of_TV
#print axioms Opt.MidVal.MR.inB
#print axioms Opt.MidVal.AtEnd.ops
#print axioms Opt.MidVal.AtEnd.regs_congr
#print axioms Opt.MidVal.AtEnd.of_rel
#print axioms Opt.MidVal.rel_enter
#print axioms Opt.MidVal.end_step
#print axioms Opt.MidVal.rel_term
#print axioms Opt.MidVal.pair_regs
#print axioms Opt.MidVal.tcont
#print axioms Opt.MidVal.hcont
#print axioms Opt.MidVal.rel_try
-- (5) MidValSim
#print axioms Opt.MidVal.Rel.bodies
#print axioms Opt.MidVal.removeOk_call
#print axioms Opt.MidVal.removeOk_callIndirect
#print axioms Opt.MidVal.step_cons
#print axioms Opt.MidVal.Rel.inB
#print axioms Opt.MidVal.Win.next
#print axioms Opt.MidVal.ContM.win
#print axioms Opt.MidVal.entry_rel
#print axioms Opt.MidVal.isSimMU
#print axioms Opt.MidVal.check_sound_norm
#print axioms Opt.MidVal.check_soundSyms_norm
#print axioms Opt.MidVal.check_soundSyms
#print axioms Opt.MidVal.check_sound
-- stage 2, family 1: constant evaluation (MidValNormConst)
#print axioms Opt.MidVal.evalInst_isPure_frame
#print axioms Opt.MidVal.mapM_lookup
#print axioms Opt.MidVal.tmVal_of_constOf
#print axioms Opt.MidVal.normSound_evalConst
-- stage 2, family 2: single-node algebraic rules (MidValNormAlg)
#print axioms Opt.MidVal.guard_spec
#print axioms Opt.MidVal.normSound_guard
#print axioms Opt.MidVal.normSound_orElse
#print axioms Opt.MidVal.ruleSound_orElse
#print axioms Opt.MidVal.nodeAt_spec
#print axioms Opt.MidVal.findTm_spec
#print axioms Opt.MidVal.tmVal_node'
#print axioms Opt.MidVal.constAt_spec
#print axioms Opt.MidVal.evalNode_some_iff
#print axioms Opt.MidVal.evalNode_iconst
#print axioms Opt.MidVal.evalNode_select
#print axioms Opt.MidVal.evalNode_uextend
#print axioms Opt.MidVal.evalNode_icmp
#print axioms Opt.MidVal.truthy_bool8
#print axioms Opt.MidVal.intcc_inv
#print axioms Opt.MidVal.truthy_bool8'
#print axioms Opt.MidVal.evalNode_icmp_inv
#print axioms Opt.MidVal.evalNode_icmp_bool
#print axioms Opt.MidVal.select_bool8
#print axioms Opt.MidVal.uextend_bool8
#print axioms Opt.MidVal.uextend_bool8'
#print axioms Opt.MidVal.select_bool8'
#print axioms Opt.MidVal.selPick_spec
#print axioms Opt.MidVal.ruleSound_selIcmp
#print axioms Opt.MidVal.evalNode_binary_nonShift
#print axioms Opt.MidVal.evalNode_ishl
#print axioms Opt.MidVal.mul_pow2
#print axioms Opt.MidVal.pow2Log_spec
#print axioms Opt.MidVal.ruleSound_mulPow2
#print axioms Opt.MidVal.evalNode_stackAddr
#print axioms Opt.MidVal.add_stack_eq
#print axioms Opt.MidVal.ruleSound_addStack
#print axioms Opt.MidVal.evalNode_extend
#print axioms Opt.MidVal.evalNode_ireduce
#print axioms Opt.MidVal.evalNode_ty_of_nodeTy
#print axioms Opt.MidVal.setWidth_extOp
#print axioms Opt.MidVal.extOp_narrow
#print axioms Opt.MidVal.extOp_same
#print axioms Opt.MidVal.ruleSound_redExt
#print axioms Opt.MidVal.ruleSound_algStep
#print axioms Opt.MidVal.normSound_alg
#print axioms Opt.MidVal.normSound_std
-- (5) MidValProg
#print axioms Opt.MidVal.checked_simMU
#print axioms Opt.MidVal.Validated.funsSimMU
#print axioms Opt.MidVal.checkedSyms_simMUAt
#print axioms Opt.MidVal.ValidatedSyms.funsSimMUAt
#print axioms Opt.MidVal.validated_refines_syms
#print axioms Opt.MidVal.validated_refines
-- (5) MidValNeg
#print axioms Opt.LStar.of_no_next
#print axioms Opt.FunSimMU.entry_rel
#print axioms Opt.not_funSimMU_trap
#print axioms Opt.LStar.det
#print axioms Opt.IsSimM.ret_eq
#print axioms Opt.not_funSimMU_ret_ne
#print axioms Opt.not_funSimMU_call_ret
#print axioms Opt.not_funSimMU_ret
-- witnesses: the real pair (native_decide of the re-check) and the negative pairs
#print axioms Opt.MidVal.RealWitness.pair_checked -- witness: native_decide
#print axioms Opt.MidVal.RealWitness.pair_some -- witness: native_decide
#print axioms Opt.MidVal.RealWitness.real_simMU -- witness: native_decide
#print axioms Opt.MidVal.RealWitness.real_refines -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.deadF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.deadG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.dead_not_sim
#print axioms Opt.MidVal.NegWitness.dead_rejected
#print axioms Opt.MidVal.NegWitness.stF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.stG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.st_not_sim
#print axioms Opt.MidVal.NegWitness.st_rejected
#print axioms Opt.MidVal.NegWitness.hoF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.hoG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.ho_not_sim
#print axioms Opt.MidVal.NegWitness.ho_rejected
#print axioms Opt.MidVal.NegWitness.enF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.enG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.en_not_sim
#print axioms Opt.MidVal.NegWitness.en_rejected
#print axioms Opt.MidVal.NegWitness.mgF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.mgG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.mg_not_sim
#print axioms Opt.MidVal.NegWitness.mg_rejected
#print axioms Opt.MidVal.NegWitness.roF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.roG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.ro_not_sim
#print axioms Opt.MidVal.NegWitness.ro_rejected
#print axioms Opt.MidVal.NegWitness.caF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.caG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.ca_not_sim
#print axioms Opt.MidVal.NegWitness.ca_rejected
#print axioms Opt.MidVal.NegWitness.tyF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.tyG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.ty_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.pair_of
#print axioms Opt.MidVal.GapWitness.callind_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.callind_checked -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.callind_simMU -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.bitcast_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.bitcast_checked -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.bitcast_simMU -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.hoist_plain_rejects -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.hoist_checked -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.hoist_checked_std -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.hoist_resolves -- witness: native_decide
#print axioms Opt.MidVal.GapWitness.hoist_sim -- witness: native_decide
-- witnesses of constant evaluation (FVTest/Opt/MidValNormWitness.lean)
#print axioms Opt.MidVal.NormWitness.pos_shift -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.pos_shift_id_rejects -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.neg_shift -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.pos_sshr -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.pos_sshr_id_rejects -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.neg_sshr -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.shiftF_text -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.shiftG0_text -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.sshrF_text -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.sshrG40_text -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.real_id_rejects -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.real_checked -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.real_some -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.real_simMU -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.real_refines -- witness: native_decide
#print axioms Opt.MidVal.NormWitness.shift_not_sim
#print axioms Opt.MidVal.NormWitness.shift_rejected
#print axioms Opt.MidVal.NormWitness.sshr_not_sim
#print axioms Opt.MidVal.NormWitness.sshr_rejected
-- witnesses of the algebraic rules (FVTest/Opt/MidValAlgWitness.lean)
#print axioms Opt.MidVal.AlgWitness.pos_sel -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_sel_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.neg_sel -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_mul -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_mul_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.neg_mul -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_stack -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_stack_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.neg_stack -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_red -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.pos_red_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.neg_red -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.selNegF_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.selNegG_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.redF_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.redGu_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.sel_not_sim
#print axioms Opt.MidVal.AlgWitness.sel_rejected
#print axioms Opt.MidVal.AlgWitness.red_not_sim
#print axioms Opt.MidVal.AlgWitness.red_rejected
#print axioms Opt.MidVal.AlgWitness.sim_of_checked
#print axioms Opt.MidVal.AlgWitness.real_mul_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_mul_checked -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_mul_sim -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_stack_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_stack_checked -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_stack_sim -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_sel_const_rejects -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_sel_checked -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.real_sel_sim -- witness: native_decide
-- (no axioms at all: last, so the audit's parser does not join them with the next line)
#print axioms Opt.SemSimMWitness.keeps
#print axioms Opt.SemSimMWitness.fwd_entry
#print axioms Opt.MidVal.LeP.refl
#print axioms Opt.MidVal.LeP.mono
#print axioms Opt.MidVal.LeP.of_anc
#print axioms Opt.MidVal.avail_of_leP
#print axioms Opt.MidVal.leP_of_avail
#print axioms Opt.MidVal.ty_width_bytes
#print axioms Opt.MidVal.Tn.mbc
#print axioms Opt.MidVal.Tn.ofRes_cases
