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
import FVTest.Opt.MidValAlg2Witness
import FV.Opt.Proof.MidValCondProg
import FVTest.Opt.MidValCondWitness
import FV.Opt.Proof.MidValNormTyped
import FVTest.Opt.MidValTypedWitness
import FV.Opt.Proof.MidValNormFam4
import FVTest.Opt.MidValFam4Witness
import FV.Opt.Proof.MidValFold
import FVTest.Opt.MidValFoldWitness
import FV.Opt.Proof.MidValDiv
import FVTest.Opt.MidValDivWitness
import FV.Opt.Proof.MidValPhi
import FVTest.Opt.MidValPhiWitness
import FVTest.Opt.MidValPhiMWitness
import FVTest.Opt.MidValZeroWitness
import FV.Opt.Proof.MidValNormFam5
import FVTest.Opt.MidValFam5Witness
import FV.Opt.Proof.MidValMagic
import FVTest.Opt.MidValMagicWitness
import FV.Opt.Proof.MidValNormFam6
import FVTest.Opt.MidValFam6Witness
import FV.Opt.Proof.MidValNormDrop
import FVTest.Opt.MidValDropWitness

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
-- stage 2, family 2, second set (MidValNormAlg2)
#print axioms Opt.MidVal.nodeSound_orElse
#print axioms Opt.MidVal.evalNode_unary
#print axioms Opt.MidVal.evalNode_bmask
#print axioms Opt.MidVal.tmVal_res
#print axioms Opt.MidVal.intcc_swap
#print axioms Opt.MidVal.ns_icmpSwap
#print axioms Opt.MidVal.one_ne_zero_of_pos
#print axioms Opt.MidVal.boolAt_val
#print axioms Opt.MidVal.icmp_bool_keep
#print axioms Opt.MidVal.icmp_bool_flip
#print axioms Opt.MidVal.ns_icmpBool
#print axioms Opt.MidVal.toNat_one_of_pos
#print axioms Opt.MidVal.ult_one
#print axioms Opt.MidVal.uge_one
#print axioms Opt.MidVal.ugt_zero
#print axioms Opt.MidVal.ule_zero
#print axioms Opt.MidVal.ns_icmpUnit
#print axioms Opt.MidVal.add_self_eq_mul_two
#print axioms Opt.MidVal.ns_subNeg
#print axioms Opt.MidVal.ns_mulTwo
#print axioms Opt.MidVal.shl_one
#print axioms Opt.MidVal.ns_shlOne
#print axioms Opt.MidVal.ns_xorNot
#print axioms Opt.MidVal.ns_bmaskBool
#print axioms Opt.MidVal.ruleSound_algStep2
#print axioms Opt.MidVal.normSound_alg2
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
#print axioms Opt.MidVal.NegWitness.shF_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.shG_text -- witness: native_decide
#print axioms Opt.MidVal.NegWitness.sh_not_sim
#print axioms Opt.MidVal.NegWitness.sh_rejected
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
#print axioms Opt.MidVal.AlgWitness.neg_redAtom -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.selNegF_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.selNegG_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.redF_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.redGu_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.redAtomF_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.redAtomG_text -- witness: native_decide
#print axioms Opt.MidVal.AlgWitness.sel_not_sim
#print axioms Opt.MidVal.AlgWitness.sel_rejected
#print axioms Opt.MidVal.AlgWitness.red_not_sim
#print axioms Opt.MidVal.AlgWitness.red_rejected
#print axioms Opt.MidVal.AlgWitness.redAtom_not_sim
#print axioms Opt.MidVal.AlgWitness.redAtom_rejected
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
-- witnesses of the second set (FVTest/Opt/MidValAlg2Witness.lean)
#print axioms Opt.MidVal.Alg2Witness.pos_swap -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.swap_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_swap -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_bool -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.bool_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_bool -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_unit -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.unit_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_unit -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_sub -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.sub_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_sub -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_mul2 -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.mul2_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_shl1 -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_mul2 -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_bmask -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.bmask_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_bmask -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.pos_xor -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.xor_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.neg_xor -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.boolF2_text -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.boolG_text -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.unitF2_text -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.unitG_text -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.bmaskF2_text -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.bmaskG2_text -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.bool_not_sim
#print axioms Opt.MidVal.Alg2Witness.bool_rejected
#print axioms Opt.MidVal.Alg2Witness.unit_not_sim
#print axioms Opt.MidVal.Alg2Witness.unit_rejected
#print axioms Opt.MidVal.Alg2Witness.bmask_not_sim
#print axioms Opt.MidVal.Alg2Witness.bmask_rejected
#print axioms Opt.MidVal.Alg2Witness.real_sub_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_sub_checked -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_sub_sim -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_mul2_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_mul2_checked -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_mul2_sim -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_swap_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_swap_checked -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_swap_sim -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_unit_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_unit_checked -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_unit_sim -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_bool_alg2_needed -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_bool_checked -- witness: native_decide
#print axioms Opt.MidVal.Alg2Witness.real_bool_sim -- witness: native_decide
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
-- #1119 stage 2 family 3 (route D): branch conditions (FV/Opt/Proof/MidValCondSim.lean, MidValCondProg.lean)
#print axioms Opt.MidVal.evalInst_chain_trap
#print axioms Opt.MidVal.evalInst_chain_mem
#print axioms Opt.MidVal.RunS.append
#print axioms Opt.MidVal.RunS.congr
#print axioms Opt.MidVal.truthy_bool8
#print axioms Opt.MidVal.zeroExtend_eq_zero
#print axioms Opt.MidVal.signExtend_eq_zero
#print axioms Opt.MidVal.truthy_zeroExtend
#print axioms Opt.MidVal.truthy_signExtend
#print axioms Opt.MidVal.ult_zero_left
#print axioms Opt.MidVal.truthy_icmp_zero
#print axioms Opt.MidVal.ChainOK.comp
#print axioms Opt.MidVal.ChainOK.nil
#print axioms Opt.MidVal.wrap_ok
#print axioms Opt.MidVal.prepChain_ok
#print axioms Opt.MidVal.prepChain_res
#print axioms Opt.MidVal.PrepRel.refl
#print axioms Opt.MidVal.prepBlock_rel
#print axioms Opt.MidVal.prepBlocks_rel
#print axioms Opt.MidVal.condPrep_rel
#print axioms Opt.MidVal.refsOk_spec
#print axioms Opt.MidVal.CR.enter
#print axioms Opt.MidVal.CR.enter_same
#print axioms Opt.MidVal.CR.after
#print axioms Opt.MidVal.CR.stepA
#print axioms Opt.MidVal.CR.stepB
#print axioms Opt.MidVal.ofRes_enter_next
#print axioms Opt.MidVal.ofRes_enter_ne
#print axioms Opt.MidVal.ofRes_get_ne
#print axioms Opt.MidVal.CR.stepC
#print axioms Opt.MidVal.freshValue_le_of_bound
#print axioms Opt.MidVal.prepBlocks_mem
#print axioms Opt.MidVal.condPrep_freshValue
#print axioms Opt.MidVal.agree_tryRets
#print axioms Opt.MidVal.CR.isSimWU
#print axioms Opt.MidVal.condPrep_simU
#print axioms Opt.MidVal.check_soundC_norm
#print axioms Opt.MidVal.check_soundC
#print axioms Opt.MidVal.check_soundSymsC
#print axioms Opt.MidVal.checkCertC_nil
#print axioms Opt.MidVal.checkedC_simMU
#print axioms Opt.MidVal.checkedSymsC_simMUAt
#print axioms Opt.MidVal.Validated.toC
#print axioms Opt.MidVal.ValidatedC.funsSimMU
#print axioms Opt.MidVal.validatedC_refines
#print axioms Opt.MidVal.ValidatedSyms.toC
#print axioms Opt.MidVal.ValidatedSymsC.funsSimMUAt
#print axioms Opt.MidVal.validatedC_refines_syms
-- witnesses of family 3 (FVTest/Opt/MidValCondWitness.lean)
#print axioms Opt.MidVal.CondWitness.pos_ne -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.pos_ne_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.pos_ext -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.pos_ext_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.neg_eq -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.neg_ugt1 -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.eqF_text -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.neG_text -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.eq_not_sim
#print axioms Opt.MidVal.CondWitness.eq_rejected
#print axioms Opt.MidVal.CondWitness.ugt1F_text -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.ugt1_not_sim
#print axioms Opt.MidVal.CondWitness.ugt1_rejected
#print axioms Opt.MidVal.CondWitness.simC_of_checked
#print axioms Opt.MidVal.CondWitness.real_ext_plain_rejects -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.real_ext_checked -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.real_ext_sim -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.real_ne_plain_rejects -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.real_ne_checked -- witness: native_decide
#print axioms Opt.MidVal.CondWitness.real_ne_sim -- witness: native_decide
-- #1119 stage 2, the typed normaliser seam (FV/Opt/Proof/MidValTerm.lean, MidValTyped.lean,
-- MidValNormTyped.lean; the `…T` versions of the simulation lemmas take `HypT`)
#print axioms Opt.MidVal.NormSound.toT
#print axioms Opt.MidVal.atomTy_tm
#print axioms Opt.MidVal.reach_site
#print axioms Opt.MidVal.atomsTyped_of
#print axioms Opt.MidVal.Hyp.toT
#print axioms Opt.MidVal.HypT.wff
#print axioms Opt.MidVal.HypT.wfg
#print axioms Opt.MidVal.HypT.idomF
#print axioms Opt.MidVal.HypT.idomG
#print axioms Opt.MidVal.HypT.idomC
#print axioms Opt.MidVal.HypT.rankF
#print axioms Opt.MidVal.HypT.le_sound
#print axioms Opt.MidVal.HypT.leP_trans
#print axioms Opt.MidVal.HypT.siteF
#print axioms Opt.MidVal.HypT.TV_stable
#print axioms Opt.MidVal.HypT.atomsTyped
#print axioms Opt.MidVal.FactHolds.stableT
#print axioms Opt.MidVal.rel_entryT
#print axioms Opt.MidVal.entry_facts_holdT
#print axioms Opt.MidVal.FStep.regs_afterT
#print axioms Opt.MidVal.FStep.TV_afterT
#print axioms Opt.MidVal.FStep.rel_afterT
#print axioms Opt.MidVal.FStep.TV_pureOkT
#print axioms Opt.MidVal.rel_nopT
#print axioms Opt.MidVal.rel_pureT
#print axioms Opt.MidVal.rel_removeT
#print axioms Opt.MidVal.MCtx.evalT
#print axioms Opt.MidVal.MCtx.callT
#print axioms Opt.MidVal.rel_bindT
#print axioms Opt.MidVal.facts_nextT
#print axioms Opt.MidVal.matched_nextT
#print axioms Opt.MidVal.matched_trapT
#print axioms Opt.MidVal.matched_callT
#print axioms Opt.MidVal.matched_ciT
#print axioms Opt.MidVal.rel_matchedT
#print axioms Opt.MidVal.results_lenT
#print axioms Opt.MidVal.gStepT
#print axioms Opt.MidVal.gStmtT
#print axioms Opt.MidVal.gPre_run_listT
#print axioms Opt.MidVal.gPre_runT
#print axioms Opt.MidVal.Tn.id_eqT
#print axioms Opt.MidVal.Tn.block?_gT
#print axioms Opt.MidVal.Tn.strict_of_leT
#print axioms Opt.MidVal.Tn.strict_of_ancT
#print axioms Opt.MidVal.Tn.TV_enterT
#print axioms Opt.MidVal.AtEnd.opsT
#print axioms Opt.MidVal.AtEnd.regs_congrT
#print axioms Opt.MidVal.AtEnd.of_relT
#print axioms Opt.MidVal.rel_enterT
#print axioms Opt.MidVal.end_stepT
#print axioms Opt.MidVal.rel_termT
#print axioms Opt.MidVal.pair_regsT
#print axioms Opt.MidVal.tcontT
#print axioms Opt.MidVal.hcontT
#print axioms Opt.MidVal.rel_tryT
#print axioms Opt.MidVal.step_consT
#print axioms Opt.MidVal.isSimMUT
#print axioms Opt.MidVal.entry_relT
#print axioms Opt.MidVal.check_sound_normT
#print axioms Opt.MidVal.check_soundSyms_normT
#print axioms Opt.MidVal.check_soundC_normT
-- #1119 family 7, the normaliser seam with defined operands (FV/Opt/Proof/MidValTerm.lean,
-- MidValRel.lean; the `…D` versions of the simulation lemmas take `HypD`, the `…T` ones are
-- their corollaries)
#print axioms Opt.MidVal.NormSoundT.toD
#print axioms Opt.MidVal.HypT.toD
#print axioms Opt.MidVal.HypD.wff
#print axioms Opt.MidVal.HypD.wfg
#print axioms Opt.MidVal.HypD.idomF
#print axioms Opt.MidVal.HypD.idomG
#print axioms Opt.MidVal.HypD.idomC
#print axioms Opt.MidVal.HypD.rankF
#print axioms Opt.MidVal.HypD.le_sound
#print axioms Opt.MidVal.HypD.leP_trans
#print axioms Opt.MidVal.HypD.siteF
#print axioms Opt.MidVal.HypD.TV_stable
#print axioms Opt.MidVal.HypD.atomsTyped
#print axioms Opt.MidVal.FactHolds.stableD
#print axioms Opt.MidVal.rel_entryD
#print axioms Opt.MidVal.entry_facts_holdD
#print axioms Opt.MidVal.FStep.regs_afterD
#print axioms Opt.MidVal.FStep.TV_afterD
#print axioms Opt.MidVal.FStep.rel_afterD
#print axioms Opt.MidVal.FStep.TV_pureOkD
#print axioms Opt.MidVal.rel_nopD
#print axioms Opt.MidVal.rel_pureD
#print axioms Opt.MidVal.rel_removeD
#print axioms Opt.MidVal.MCtx.evalD
#print axioms Opt.MidVal.MCtx.callD
#print axioms Opt.MidVal.rel_bindD
#print axioms Opt.MidVal.facts_nextD
#print axioms Opt.MidVal.matched_nextD
#print axioms Opt.MidVal.matched_trapD
#print axioms Opt.MidVal.matched_callD
#print axioms Opt.MidVal.matched_ciD
#print axioms Opt.MidVal.rel_matchedD
#print axioms Opt.MidVal.results_lenD
#print axioms Opt.MidVal.gStepD
#print axioms Opt.MidVal.gStmtD
#print axioms Opt.MidVal.gPre_run_listD
#print axioms Opt.MidVal.gPre_runD
#print axioms Opt.MidVal.Tn.id_eqD
#print axioms Opt.MidVal.Tn.block?_gD
#print axioms Opt.MidVal.Tn.strict_of_leD
#print axioms Opt.MidVal.Tn.strict_of_ancD
#print axioms Opt.MidVal.Tn.TV_enterD
#print axioms Opt.MidVal.AtEnd.opsD
#print axioms Opt.MidVal.AtEnd.regs_congrD
#print axioms Opt.MidVal.AtEnd.of_relD
#print axioms Opt.MidVal.rel_enterD
#print axioms Opt.MidVal.end_stepD
#print axioms Opt.MidVal.rel_termD
#print axioms Opt.MidVal.pair_regsD
#print axioms Opt.MidVal.tcontD
#print axioms Opt.MidVal.hcontD
#print axioms Opt.MidVal.rel_tryD
#print axioms Opt.MidVal.step_consD
#print axioms Opt.MidVal.isSimMUD
#print axioms Opt.MidVal.entry_relD
#print axioms Opt.MidVal.check_sound_normD
#print axioms Opt.MidVal.check_soundSyms_normD
#print axioms Opt.MidVal.check_soundC_normD
-- #1119 family 7, operand-dropping rewrites (FV/Opt/Proof/MidValNormDrop.lean)
#print axioms Opt.MidVal.normSoundD_guard
#print axioms Opt.MidVal.normSoundD_orElse
#print axioms Opt.MidVal.evalNode_bin_of
#print axioms Opt.MidVal.tmVal_bin_ops
#print axioms Opt.MidVal.add_sub_left
#print axioms Opt.MidVal.add_sub_right
#print axioms Opt.MidVal.sub_add_right
#print axioms Opt.MidVal.sub_add_left
#print axioms Opt.MidVal.subAdd_spec
#print axioms Opt.MidVal.addSubPick_spec
#print axioms Opt.MidVal.ruleSoundD_subAdd
#print axioms Opt.MidVal.ruleSoundD_addSub
#print axioms Opt.MidVal.rAbsorb_spec
#print axioms Opt.MidVal.rAbsorb_comm
#print axioms Opt.MidVal.rAbsorb_nonShift
#print axioms Opt.MidVal.absPick_spec
#print axioms Opt.MidVal.ruleSoundD_absTyped
#print axioms Opt.MidVal.ruleSoundD_dropStep
#print axioms Opt.MidVal.normSoundD_stdD
#print axioms Opt.MidVal.normSoundT_guard
#print axioms Opt.MidVal.normSoundT_orElse
#print axioms Opt.MidVal.tyAt_val
#print axioms Opt.MidVal.selCC_spec
#print axioms Opt.MidVal.icmp_zero_ne
#print axioms Opt.MidVal.icmp_zero_eq
#print axioms Opt.MidVal.select_one_zero
#print axioms Opt.MidVal.select_zero_one
#print axioms Opt.MidVal.ruleSoundT_selTyped
#print axioms Opt.MidVal.ruleSoundT_redTyped
#print axioms Opt.MidVal.ruleSoundT_typedStep
#print axioms Opt.MidVal.normSoundT_typed
-- #1119 stage 2, family 4 (FV/Opt/Proof/MidValNormFam4.lean)
#print axioms Opt.MidVal.tmVal_same
#print axioms Opt.MidVal.tyAt_ops
#print axioms Opt.MidVal.rNeutral_spec
#print axioms Opt.MidVal.commOp_spec
#print axioms Opt.MidVal.setWidth_ring
#print axioms Opt.MidVal.idPick_spec
#print axioms Opt.MidVal.ruleSoundT_idStep
#print axioms Opt.MidVal.foldAdd_spec
#print axioms Opt.MidVal.affPlan_spec
#print axioms Opt.MidVal.ruleSound_affStep
#print axioms Opt.MidVal.ruleSound_swapStep
#print axioms Opt.MidVal.TmReach.of_ops
#print axioms Opt.MidVal.AtomsTyped.of_ops
#print axioms Opt.MidVal.redOf_spec
#print axioms Opt.MidVal.ruleSoundT_narrowStep
#print axioms Opt.MidVal.normSoundT_base
#print axioms Opt.MidVal.normSoundT_narrowN
#print axioms Opt.MidVal.normSoundT_stdT
-- witnesses of the typed rules (FVTest/Opt/MidValTypedWitness.lean)
#print axioms Opt.MidVal.TypedWitness.pos_sel -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_sel_std_rejects -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.neg_sel -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_red -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_red_std_rejects -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_redU -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_redU_std_rejects -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_redR -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.pos_redR_std_rejects -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.neg_red -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.selNegF_text -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.selNegG_text -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.redNegF_text -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.redNegG_text -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.sel_not_sim
#print axioms Opt.MidVal.TypedWitness.sel_rejected
#print axioms Opt.MidVal.TypedWitness.red_not_sim
#print axioms Opt.MidVal.TypedWitness.red_rejected
#print axioms Opt.MidVal.TypedWitness.real_red_std_rejects -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.real_red_checked -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.real_red_sim -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.real_sel_std_rejects -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.real_sel_checked -- witness: native_decide
#print axioms Opt.MidVal.TypedWitness.real_sel_sim -- witness: native_decide
-- witnesses of family 4 (FVTest/Opt/MidValFam4Witness.lean)
#print axioms Opt.MidVal.Fam4Witness.pos_id -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_id_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_idL -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_idL_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.neg_idOne -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.neg_idSubL -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_aff -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_aff_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.neg_aff -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_swap -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_swap_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.neg_swap -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_narrow -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.pos_narrow_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.neg_narrow -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.idOneF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.idSubLF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.idG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.affF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.affNegG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.swapNegF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.swapNegG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.narrowNegF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.narrowNegG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.idOne_not_sim
#print axioms Opt.MidVal.Fam4Witness.idOne_rejected
#print axioms Opt.MidVal.Fam4Witness.idSubL_not_sim
#print axioms Opt.MidVal.Fam4Witness.idSubL_rejected
#print axioms Opt.MidVal.Fam4Witness.aff_not_sim
#print axioms Opt.MidVal.Fam4Witness.aff_rejected
#print axioms Opt.MidVal.Fam4Witness.swap_not_sim
#print axioms Opt.MidVal.Fam4Witness.swap_rejected
#print axioms Opt.MidVal.Fam4Witness.narrow_not_sim
#print axioms Opt.MidVal.Fam4Witness.narrow_rejected
#print axioms Opt.MidVal.Fam4Witness.idStep_fires -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.idStep_frame -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.idStep_not_normSound -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.narrowStep_fires -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.narrowStep_frame -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.narrowStep_not_normSound -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_id_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_id_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_id_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_aff_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_aff_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_aff_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_swap_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_swap_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_swap_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_narrow_t0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_narrow_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam4Witness.real_narrow_sim -- witness: native_decide

-- #1119 rewrite:blocks: constant-condition branch folding (FV/Opt/Proof/MidValFold.lean); the
-- check_soundC_* theorems above are re-proved through checkCertC's fold requests (MidValCondProg.lean)
#print axioms Opt.MidVal.kInv_empty
#print axioms Opt.MidVal.kInv_set
#print axioms Opt.MidVal.kOk_spec
#print axioms Opt.MidVal.constEval_pure
#print axioms Opt.MidVal.constEval_sound
#print axioms Opt.MidVal.kInv_stmt
#print axioms Opt.MidVal.kOk_none
#print axioms Opt.MidVal.foldFn_freshValue
#print axioms Opt.MidVal.foldFn_block?
#print axioms Opt.MidVal.foldFn_entry?
#print axioms Opt.MidVal.foldBlock_term
#print axioms Opt.MidVal.getMany_fold
#print axioms Opt.MidVal.get_fold
#print axioms Opt.MidVal.callArgs_fold
#print axioms Opt.MidVal.tailArgs_fold
#print axioms Opt.MidVal.ciArgs_fold
#print axioms Opt.MidVal.tcArgs_fold
#print axioms Opt.MidVal.ticArgs_fold
#print axioms Opt.MidVal.FR.enter
#print axioms Opt.MidVal.FR.stepA
#print axioms Opt.MidVal.FR.stepC
#print axioms Opt.MidVal.kNone_window
#print axioms Opt.MidVal.FR.term_try
#print axioms Opt.MidVal.FR.isSimU
#print axioms Opt.MidVal.foldFn_simU
#print axioms Opt.MidVal.kLook_lt
#print axioms Opt.MidVal.foldBr_simU
#print axioms Opt.MidVal.foldPre_simU
-- witnesses (FVTest/Opt/MidValFoldWitness.lean)
#print axioms Opt.MidVal.FoldWitness.pos_ult -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_ult_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_ult_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_cross -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_cross_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_cross_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_table -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_table_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.pos_table_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.ultF_text -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.ult_blocks -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.paramF_text -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.ultG_text -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.param_not_folded -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.neg_param -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.param_not_sim
#print axioms Opt.MidVal.FoldWitness.param_rejected
#print axioms Opt.MidVal.FoldWitness.keepWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.neg_keep_wrong -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.keep_wrong_not_sim
#print axioms Opt.MidVal.FoldWitness.keep_wrong_rejected
#print axioms Opt.MidVal.FoldWitness.tableF_text -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.tableWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.neg_table -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.table_not_sim
#print axioms Opt.MidVal.FoldWitness.table_rejected
#print axioms Opt.MidVal.FoldWitness.real_mul_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_mul_checked -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_mul_sim -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_table_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_table_checked -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_table_sim -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_dom_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_dom_checked -- witness: native_decide
#print axioms Opt.MidVal.FoldWitness.real_dom_sim -- witness: native_decide

-- #1119 skeleton-removed div: division by a constant (FV/Opt/Proof/MidValDiv.lean; foldPre_simU
-- above now goes through divPre_simU)
#print axioms Opt.MidVal.log2Exact_spec
#print axioms Opt.MidVal.twoPow_of_toNat
#print axioms Opt.MidVal.udiv_pow2
#print axioms Opt.MidVal.urem_pow2
#print axioms Opt.MidVal.divRw_spec
#print axioms Opt.MidVal.divBody_supply
#print axioms Opt.MidVal.bodyRel_cons
#print axioms Opt.MidVal.divBlocks_find
#print axioms Opt.MidVal.divBlocks_head
#print axioms Opt.MidVal.supOk_of
#print axioms Opt.MidVal.DR.enter
#print axioms Opt.MidVal.div_step
#print axioms Opt.MidVal.div_only_next
#print axioms Opt.MidVal.kInv_next
#print axioms Opt.MidVal.DR.stepA
#print axioms Opt.MidVal.DR.stepC
#print axioms Opt.MidVal.DR.isSimU
#print axioms Opt.MidVal.divFn_simU
#print axioms Opt.MidVal.divPre_simU
-- witnesses (FVTest/Opt/MidValDivWitness.lean)
#print axioms Opt.MidVal.DivWitness.pos_udiv -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_udiv_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_udiv_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_urem -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_urem_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_urem_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_udiv1 -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_udiv1_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_sdiv1 -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.pos_sdiv1_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.udiv8_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.sdiv8_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.urem8_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.ushr2_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.ushr3_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.sshr3_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.band8_text -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.not_sim_at
#print axioms Opt.MidVal.DivWitness.shift_not_sim
#print axioms Opt.MidVal.DivWitness.neg_shift -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.shift_rejected
#print axioms Opt.MidVal.DivWitness.sdiv_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.signed_not_sim
#print axioms Opt.MidVal.DivWitness.neg_signed -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.signed_rejected
#print axioms Opt.MidVal.DivWitness.unsigned_not_sim
#print axioms Opt.MidVal.DivWitness.neg_unsigned -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.unsigned_rejected
#print axioms Opt.MidVal.DivWitness.mask_not_sim
#print axioms Opt.MidVal.DivWitness.neg_mask -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.mask_rejected
#print axioms Opt.MidVal.DivWitness.div0_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.sdivm1_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.neg_div0 -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.neg_sdivm1 -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_urem_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_urem_checked -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_urem_sim -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_udiv_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_udiv_checked -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_udiv_sim -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_urem32_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_urem32_checked -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_urem32_sim -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_one_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_one_checked -- witness: native_decide
#print axioms Opt.MidVal.DivWitness.real_one_sim -- witness: native_decide

-- #1119 removed block parameters: the validator's constant-phi removal (FV/Opt/Proof/MidValPhi.lean;
-- foldPre_simU above now goes through phiPre_simU)
#print axioms Opt.MidVal.phiOk_facts
#print axioms Opt.MidVal.phiOk_simU
#print axioms Opt.MidVal.phiPre_simU
-- witnesses (FVTest/Opt/MidValPhiWitness.lean)
#print axioms Opt.MidVal.PhiWitness.try_params -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.pos_try -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.pos_try_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.twoF_text -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.wrongG_text -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.two_phiPre -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.two_phiOk_wrong -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.neg_two -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.two_not_sim
#print axioms Opt.MidVal.PhiWitness.two_rejected
#print axioms Opt.MidVal.PhiWitness.real_bigint_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_bigint_checked -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_bigint_sim -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_dissimilar_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_dissimilar_checked -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_dissimilar_sim -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_criterion_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_criterion_checked -- witness: native_decide
#print axioms Opt.MidVal.PhiWitness.real_criterion_sim -- witness: native_decide

-- #1119 removed block parameters in functions with a call_indirect (FV/Opt/Proof/MidValPhiM.lean;
-- phiPre_simU above now also goes through phiOkM_simU)
#print axioms Opt.ConstPhi.CRel.ciM
#print axioms Opt.ConstPhi.CR.isSimWUM
#print axioms Opt.MidVal.phiOkM_facts
#print axioms Opt.MidVal.phiOkM_simU
-- witnesses (FVTest/Opt/MidValPhiMWitness.lean)
#print axioms Opt.MidVal.PhiMWitness.ci_phiOk -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.ci_phiOkM -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.ci_params -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.pos_ci -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.pos_ci_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.twoMF_text -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.wrongMG_text -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.twoM_phiPre -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.twoM_phiOkM_wrong -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.neg_twoM -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.twoM_not_sim
#print axioms Opt.MidVal.PhiMWitness.twoM_rejected
#print axioms Opt.MidVal.PhiMWitness.real_proptest_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_proptest_checked -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_proptest_sim -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_toml_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_toml_checked -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_toml_sim -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_memchr_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_memchr_checked -- witness: native_decide
#print axioms Opt.MidVal.PhiMWitness.real_memchr_sim -- witness: native_decide

-- #1119 unsigned comparisons with 0 in the fold constants (FV/Opt/Proof/MidValFold.lean: zeroCmp_sound,
-- used by constEval_sound / constEval_pure)
#print axioms Opt.MidVal.zeroCmp_pure
#print axioms Opt.MidVal.kZero
#print axioms Opt.MidVal.icmp_ult_zero
#print axioms Opt.MidVal.icmp_uge_zero
#print axioms Opt.MidVal.icmp_ule_zero
#print axioms Opt.MidVal.icmp_ugt_zero
#print axioms Opt.MidVal.zeroCmp_sound
-- witnesses (FVTest/Opt/MidValZeroWitness.lean)
#print axioms Opt.MidVal.ZeroWitness.pos_ult -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ult_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ult_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ugt -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ugt_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ugt_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_uge -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_uge_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_uge_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ule -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ule_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.pos_ule_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.ugtF_text -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.ugt_not_folded -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.neg_ugt -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.ugt_not_sim
#print axioms Opt.MidVal.ZeroWitness.ugt_rejected
#print axioms Opt.MidVal.ZeroWitness.ult0_not_folded -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.neg_ult0 -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.ult1_not_folded -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.neg_ult1 -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_toml_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_toml_checked -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_toml_sim -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_ws_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_ws_checked -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_ws_sim -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_serde_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_serde_checked -- witness: native_decide
#print axioms Opt.MidVal.ZeroWitness.real_serde_sim -- witness: native_decide

-- #1119 family 5 (FV/Opt/Proof/MidValNormFam5.lean; normSoundT_base / normSoundT_narrowN /
-- normSoundT_stdT above moved there, same statements), swapped unit comparisons
-- (MidValNormAlg2.lean), parameters kept after the folds (foldPreK_simU, now in MidValMagic.lean, used by
-- check_soundC_norm / check_soundC_normT)
#print axioms Opt.MidVal.ns_icmpSwapUnit
#print axioms Opt.MidVal.regs_ineg
#print axioms Opt.MidVal.addNeg_spec
#print axioms Opt.MidVal.ns_addNeg
#print axioms Opt.MidVal.mulNegPlan_spec
#print axioms Opt.MidVal.ns_mulNeg
#print axioms Opt.MidVal.redRed_spec
#print axioms Opt.MidVal.ruleSoundT_redRed
#print axioms Opt.MidVal.ruleSoundT_fam5Step
#print axioms Opt.MidVal.foldPreK_simU
-- witnesses (FVTest/Opt/MidValFam5Witness.lean)
#print axioms Opt.MidVal.Fam5Witness.pos_addNeg -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_addNeg_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.neg_addNeg -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_mulNeg -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_mulNeg_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.neg_mulNeg -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_redRed -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_redRed_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.neg_redRed -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.addNegF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.addNegWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.addNeg_not_sim
#print axioms Opt.MidVal.Fam5Witness.addNeg_rejected
#print axioms Opt.MidVal.Fam5Witness.mulNegF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.mulNegWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.mulNeg_not_sim
#print axioms Opt.MidVal.Fam5Witness.mulNeg_rejected
#print axioms Opt.MidVal.Fam5Witness.redDropF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.redDropG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.redDrop_not_sim
#print axioms Opt.MidVal.Fam5Witness.redDrop_rejected
#print axioms Opt.MidVal.Fam5Witness.redRed_fires -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.redRed_frame -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.redRed_not_normSound -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_swapU -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_swapU_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.pos_swapU_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.neg_swapU -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.swapU1F_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.swapUG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.swapU1_not_sim
#print axioms Opt.MidVal.Fam5Witness.swapU1_rejected
#print axioms Opt.MidVal.Fam5Witness.pos_keep -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.keep_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.keep_foldPre_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.keep_foldPreK_accepts -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.neg_keep -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.keepF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.keep7G_text -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.keep7_not_sim
#print axioms Opt.MidVal.Fam5Witness.keep7_rejected
#print axioms Opt.MidVal.Fam5Witness.real_swapu_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_swapu_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_swapu_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_keep_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_keep_foldPre_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_keep_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_keep_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_addneg_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_addneg_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_addneg_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_mulneg_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_mulneg_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_mulneg_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_redred_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_redred_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam5Witness.real_redred_sim -- witness: native_decide

-- #1119 skeleton-removed div: division by a constant with magic numbers (MidValMagic.lean;
-- foldPre_simU / foldPreK_simU above moved there, same statements, now through magicPre_simU)
#print axioms Opt.MidVal.sem_ushr_ofNat
#print axioms Opt.MidVal.log2Exact_none
#print axioms Opt.MidVal.magicU_facts
#print axioms Opt.MidVal.magic_noadd0
#print axioms Opt.MidVal.magic_noadd
#print axioms Opt.MidVal.magic_add1
#print axioms Opt.MidVal.magic_add
#print axioms Opt.MidVal.urem_of_quot
#print axioms Opt.MidVal.RunS.app
#print axioms Opt.MidVal.RunS.lstar
#print axioms Opt.MidVal.uQuot_noCall
#print axioms Opt.MidVal.uQuot_run
#print axioms Opt.MidVal.uQuot_mem_dst
#print axioms Opt.MidVal.magicStmts_noCall
#print axioms Opt.MidVal.magicStmts_mem_v
#print axioms Opt.MidVal.magicStmts_run
#print axioms Opt.MidVal.magicS_facts
#print axioms Opt.MidVal.ofNat_toInt_small
#print axioms Opt.MidVal.sshr_ofNat_zero
#print axioms Opt.MidVal.eval_sshr
#print axioms Opt.MidVal.RunS.sshr
#print axioms Opt.MidVal.sFix_noCall
#print axioms Opt.MidVal.sShift_noCall
#print axioms Opt.MidVal.sQuot_noCall
#print axioms Opt.MidVal.sFix_run
#print axioms Opt.MidVal.sShift_run
#print axioms Opt.MidVal.sQuot_run
#print axioms Opt.MidVal.magicStmtsS_noCall
#print axioms Opt.MidVal.magicStmtsS_mem_v
#print axioms Opt.MidVal.magicStmtsS_run
#print axioms Opt.MidVal.magicRw_spec
#print axioms Opt.MidVal.magicBody_ge
#print axioms Opt.MidVal.bodyRelM_cons
#print axioms Opt.MidVal.magicBody_results
#print axioms Opt.MidVal.magicBlocks_find
#print axioms Opt.MidVal.magicBlocks_head
#print axioms Opt.MidVal.magicBlocks_mem
#print axioms Opt.MidVal.magicFn_block?
#print axioms Opt.MidVal.magicFn_freshValue_ge
#print axioms Opt.MidVal.refsOk_lt
#print axioms Opt.MidVal.MagR.enter
#print axioms Opt.MidVal.magic_step
#print axioms Opt.MidVal.magic_only_next
#print axioms Opt.MidVal.MagR.stepA
#print axioms Opt.MidVal.MagR.stepC
#print axioms Opt.MidVal.MagR.win_agree
#print axioms Opt.MidVal.MagR.isSimWU
#print axioms Opt.MidVal.magicFn_simU
#print axioms Opt.MidVal.magicPre_simU
-- witnesses (FVTest/Opt/MidValMagicWitness.lean)
#print axioms Opt.MidVal.MagicWitness.magicU_u32_7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.magicU_u32_10 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.magicU_u64_7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.magicU_u64_10 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.magicS_s32_7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.magicS_s64_7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_udiv3 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_udiv3_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_udiv3_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_urem3 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_urem3_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_urem3_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_udiv7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_udiv7_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_udiv7_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv7_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv7_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_srem7 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_srem7_check_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_srem7_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv3 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv3_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv7_32 -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pos_sdiv7_32_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.udiv3_text -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.low_text -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.low_not_sim
#print axioms Opt.MidVal.MagicWitness.neg_low -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.low_rejected
#print axioms Opt.MidVal.MagicWitness.sdiv7_text -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.nofix_text -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.nofix_not_sim
#print axioms Opt.MidVal.MagicWitness.neg_nofix -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.nofix_rejected
#print axioms Opt.MidVal.MagicWitness.sdiv8_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.div0_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.pow2_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.i8_not_rewritten -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_udiv10_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_udiv10_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_udiv10_sim -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_udiv24_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_udiv24_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_udiv24_sim -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_add32_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_add32_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_add32_sim -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_urem192_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_urem192_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_urem192_sim -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_add64_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_add64_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_add64_sim -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_srem100_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_srem100_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_srem100_sim -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_sdiv72_c0_rejects -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_sdiv72_checked -- witness: native_decide
#print axioms Opt.MidVal.MagicWitness.real_sdiv72_sim -- witness: native_decide

-- #1119 family 6: shifts and bitwise constants (FV/Opt/Proof/MidValNormFam6.lean; normSoundT_base /
-- normSoundT_narrowN / normSoundT_stdT above moved there from MidValNormFam5.lean, same statements;
-- narrowId_val in MidValNormFam4.lean, used by ruleSoundT_narrowStep)
#print axioms Opt.MidVal.evalNode_ireduce_ty
#print axioms Opt.MidVal.narrowId_val
#print axioms Opt.MidVal.width_dvd_256
#print axioms Opt.MidVal.width_ge_8
#print axioms Opt.MidVal.width_le_128
#print axioms Opt.MidVal.dvd_two_pow_of_ge_8
#print axioms Opt.MidVal.shiftAmt_of_low8
#print axioms Opt.MidVal.low8_setWidth
#print axioms Opt.MidVal.low8_signExtend
#print axioms Opt.MidVal.shift_congr
#print axioms Opt.MidVal.evalNode_shift
#print axioms Opt.MidVal.shift_isSome
#print axioms Opt.MidVal.ruleSoundT_shAmt
#print axioms Opt.MidVal.mulShAmt_val
#print axioms Opt.MidVal.sshiftRight_shiftLeft
#print axioms Opt.MidVal.shlPlan_val
#print axioms Opt.MidVal.ruleSound_fam6Mul
#print axioms Opt.MidVal.reOp_spec
#print axioms Opt.MidVal.rePlan_val
#print axioms Opt.MidVal.ruleSound_reStep
#print axioms Opt.MidVal.ruleSoundT_fam6Step
-- witnesses (FVTest/Opt/MidValFam6Witness.lean)
#print axioms Opt.MidVal.Fam6Witness.pos_mulShr -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_mulShr_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.neg_mulShr -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_mulShl -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_mulShl_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.neg_mulShl -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_shAmt -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_shAmt_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.neg_shAmt -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_re -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_re_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.neg_re -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_reShl -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_reShl_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.neg_reShl -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_narrow -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.pos_narrow_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.neg_narrow -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.mulShrF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.mulShrWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.mulShr_not_sim
#print axioms Opt.MidVal.Fam6Witness.mulShr_rejected
#print axioms Opt.MidVal.Fam6Witness.mulShlF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.mulShlWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.mulShl_not_sim
#print axioms Opt.MidVal.Fam6Witness.mulShl_rejected
#print axioms Opt.MidVal.Fam6Witness.shAmtF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.shAmtWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.shAmt_not_sim
#print axioms Opt.MidVal.Fam6Witness.shAmt_rejected
#print axioms Opt.MidVal.Fam6Witness.reF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.reWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.re_not_sim
#print axioms Opt.MidVal.Fam6Witness.re_rejected
#print axioms Opt.MidVal.Fam6Witness.reShlF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.reShlWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.reShl_not_sim
#print axioms Opt.MidVal.Fam6Witness.reShl_rejected
#print axioms Opt.MidVal.Fam6Witness.narrowMaskF_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.narrowG_text -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.narrow_not_sim
#print axioms Opt.MidVal.Fam6Witness.narrow_rejected
#print axioms Opt.MidVal.Fam6Witness.shAmt_fires -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.shAmt_frame -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.shAmt_not_normSound -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_amt_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_amt_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_amt_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_mul_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_mul_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_mul_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_re_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_re_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_re_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_narrow_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_narrow_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_narrow_sim -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_mulshl_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_mulshl_checked -- witness: native_decide
#print axioms Opt.MidVal.Fam6Witness.real_mulshl_sim -- witness: native_decide
-- witnesses of family 7 (FVTest/Opt/MidValDropWitness.lean)
#print axioms Opt.MidVal.DropWitness.pos_subAdd -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_subAdd_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.neg_subAdd -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_addSub -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_addSub_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.neg_addSub -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_mul0 -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_mul0_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.neg_mul0 -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_orOnes -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.pos_orOnes_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.neg_orOnes -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.subAddF_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.subAddWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.subAdd_not_sim
#print axioms Opt.MidVal.DropWitness.subAdd_rejected
#print axioms Opt.MidVal.DropWitness.addSubF_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.addSubWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.addSub_not_sim
#print axioms Opt.MidVal.DropWitness.addSub_rejected
#print axioms Opt.MidVal.DropWitness.mul0F_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.mul0WrongG_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.mul0_not_sim
#print axioms Opt.MidVal.DropWitness.mul0_rejected
#print axioms Opt.MidVal.DropWitness.orOnesF_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.orOnesWrongG_text -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.orOnes_not_sim
#print axioms Opt.MidVal.DropWitness.orOnes_rejected
#print axioms Opt.MidVal.DropWitness.dropStep_fires -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.drop_frame -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.drop_val0 -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.drop_val1 -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.drop_ty1 -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.drop_atomsTyped -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.dropStep_not_normSoundT -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_sub_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_sub_checked -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_sub_sim -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_mul0_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_mul0_checked -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_mul0_sim -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_addsub_prev_rejects -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_addsub_checked -- witness: native_decide
#print axioms Opt.MidVal.DropWitness.real_addsub_sim -- witness: native_decide
