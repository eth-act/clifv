import FV.Backend.Proof.LowerTotalT
import FV.Backend.Proof.IselPrgCtorSoundT
import FV.Backend.Proof.IselPrgCoverTermT
import FV.Backend.Proof.IselPrgHandT
import FV.Backend.Proof.IselPrgTabF64
import FV.Backend.Proof.IselPrgDriverT
import FVTest.Backend.FloatProgT
import FVTest.Link.FloatScopeInputT3F
import FVTest.Link.FloatScopeTotalT3F

-- S11 (#35) slice 8 totality: typed ISLE progress (driver totality, extern-helper model,
-- context invariant, roots, hand-checked rules, the `f64const` sub-table)
#print axioms Backend.Proof.Driver.buildCtx_okT
#print axioms Backend.Proof.Driver.lowerFunction_okT
#print axioms Backend.Proof.Prg.aextT_sound
#print axioms Backend.Proof.Prg.actorT_sound
#print axioms Backend.Proof.Prg.aidata_soundT
#print axioms Backend.Proof.Prg.pinv_buildT
#print axioms Backend.Proof.Prg.pinv_termCtxT
#print axioms Backend.Proof.Prg.pinv_tryCtxT
#print axioms Backend.Proof.Prg.stmt_rootT
#print axioms Backend.Proof.Prg.term_rootT
#print axioms Backend.Proof.Prg.try_rootT
#print axioms Backend.Proof.Prg.handRules_okT
#print axioms Backend.Proof.Prg.f64Tab_ok
-- the `f64const` rule (585), the typed table and the driver
#print axioms Backend.Proof.Prg.constant_f64_hi
#print axioms Backend.Proof.Prg.hand_585T
#print axioms Backend.Proof.Prg.handOkT
#print axioms Backend.Proof.Prg.tryCall_lastT
#print axioms Backend.Proof.Prg.prgTabT_ok
#print axioms Backend.Proof.Prg.prgTabT_f64Safe
#print axioms Backend.Proof.Prg.iselProgT_of_input
#print axioms Backend.Proof.Prg.lowerFunction_ok_inputT

-- non-vacuity witnesses
#print axioms Backend.Proof.Driver.buildCtx_okT_witness
#print axioms FloatProgT.lowerFunction_ok_inputT_witness -- witness: native_decide

-- S11f (#35): the float scope (functionETF) — lowerFunction totality from input conditions
#print axioms Backend.Proof.Prg.aextTF_sound
#print axioms Backend.Proof.Prg.stmt_rootTF
#print axioms Backend.Proof.Prg.pinv_buildTF
#print axioms Backend.Proof.Prg.prgTabTF_ok
#print axioms Backend.Proof.Prg.f64TabF_ok
#print axioms Backend.Proof.Prg.iselProgTF_of_input
#print axioms Backend.Proof.Driver.lowerFunction_okTF
#print axioms Backend.Proof.Prg.lowerFunction_ok_inputTF
#print axioms E2E.LinkCheck.lowerFunction_ok_inT3F
#print axioms E2E.FloatScopeInputT3FWitness.lowers -- witness: native_decide

-- S11f (#35) stage 2: decider-free totality over the float scope
#print axioms Backend.Proof.Driver.lowerCheck_partsTF
#print axioms Backend.Proof.Driver.lowerCheckTCF_complete
#print axioms Backend.Proof.Driver.lowBlocksC_of_lowBlocks
#print axioms Backend.Proof.Driver.certOk_completeTF
#print axioms Backend.Proof.Driver.alias_factsTF
#print axioms Backend.Proof.Driver.shapeOkTS_completeI
#print axioms Backend.Proof.Prep.prepare_okTF
#print axioms Backend.Proof.Spill.classesOkM_lowerTF
#print axioms Backend.Proof.Kill.killRunsHypTF
#print axioms Backend.Proof.Kill.tryDefsExactTF
#print axioms Backend.Proof.Kill.killFreeB_lowerTF
#print axioms E2E.spillKillFreeTF
#print axioms E2E.backend_total_emit_cleanupTF
#print axioms Backend.Proof.Driver.formsCoveredB_completeTF
#print axioms E2E.ctlSpillB_of_TF
#print axioms E2E.ctlInsts_pipelineTF
#print axioms E2E.emitConds_lowerTF
#print axioms E2E.poolReachB_of_sizeTF
#print axioms E2E.LinkCheck.poolReachB_of_T3F
#print axioms E2E.LinkCheck.resClassOkB_of_TF
#print axioms E2E.LinkCheck.lowersTCB_of_T3F
#print axioms E2E.LinkCheck.fnScopeInTCB_of_T3F
#print axioms E2E.LinkCheck.pipeCleanupT_okT3F
#print axioms E2E.LinkCheck.resultsCleanupT_ok_inT3F
-- unchanged statements, proofs now through the float-scope versions
#print axioms Backend.Proof.Driver.lowerCheckT_complete
#print axioms Backend.Proof.Kill.killRunsHypT
#print axioms Backend.Proof.Kill.tryDefsExactT
#print axioms E2E.LinkCheck.pipeCleanupT_okT
#print axioms E2E.FloatScopeTotalT3FWitness.pipeline_ok -- witness: native_decide
