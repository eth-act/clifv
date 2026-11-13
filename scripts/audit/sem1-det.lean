import FV.E2E.LinkArmDetInductionWitness
import FV.E2E.BackendTwoRunEitherKWitness

-- SEM1 determinism induction (#537, #713, #716, #729, #732; docs/plans/uninit.md §5.9)
#print axioms E2E.backend_twoRunLERWZIUPF_eitherK
#print axioms E2E.LinkSys.hcallLockXP
#print axioms E2E.LinkSys.lockRet_of
#print axioms E2E.LinkSys.callLock_of
#print axioms E2E.LinkSys.canonCallTwin
#print axioms E2E.LinkSys.twinCE_of_lockK
#print axioms E2E.LinkSys.detTabPRBE_of
#print axioms E2E.LinkSys.detTabPRBr_ofCT
#print axioms E2E.LinkSys.detPRBRU_ofC
#print axioms E2E.LinkSys.thmPRBRLE_allCRU
#print axioms E2E.LinkSys.BaseNIX.std
#print axioms E2E.LinkSys.OkDNX.stdBaseNIX
#print axioms E2E.LinkSys.detInduction
#print axioms E2E.LinkSys.thmPRBRLE_allK
#print axioms E2E.LinkSys.detRunPRBCRU_allK
#print axioms E2E.LinkSys.detPRBRU_allK
#print axioms E2E.LinkSys.callTwinCET_allK
#print axioms E2E.LinkSys.detTabPRBE_allK
#print axioms E2E.LinkSys.detTabPRBr_allK
#print axioms E2E.LinkSlotSysWitness.hookNIX_L0
#print axioms E2E.LinkSlotSysWitness.baseNIX_Lsl
#print axioms E2E.LinkSlotSysWitness.needNI_Lsl -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.detInduction_Lsl -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.detPRBRU_allK_Lsl -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.detTabPRBE_allK_Lsl -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.detTabPRBr_allK_Lsl -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.lockRet_of_Lsl -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.canonCallTwin_LslK -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.hcallLockXP_LslK -- witness: native_decide
#print axioms E2E.LinkSlotSysWitness.thmPRBRLE_allCRU_Lsl -- witness: native_decide
#print axioms E2E.TwoRunVWitness.r_twoRunLERWZIUPF_eitherK_Lsl -- witness: native_decide
#print axioms E2E.TwoRunVWitness.source_twoRunLERWZIUPF_eitherK -- witness: native_decide

-- #581 loop-form stack probes: the two-run theorems that speak only of the states after the
-- prologues, without a premise on the entries' flags (docs/contracts/e2e.md "Stack probes (loop form)")
#print axioms Backend.Proof.ProRun.flags_irrel
#print axioms Backend.Proof.proRun_flags_irrel_witness
#print axioms E2E.iterN_prologue_flagTwin
#print axioms E2E.stEqOutX_prologueZ_entry
#print axioms E2E.stEqOutX_entryZ
#print axioms E2E.backend_twoRunLE
#print axioms E2E.backend_twoRunLEF
#print axioms E2E.backend_twoRunLER
#print axioms E2E.backend_twoRunLW
#print axioms E2E.backend_twoRunLWNp
#print axioms E2E.backend_twoRunLWNpP
#print axioms E2E.backend_twoRunLWNpPK
#print axioms E2E.backend_twoRunLWNpPV
#print axioms E2E.backend_twoRunLWNpV
#print axioms E2E.backend_twoRunLWNpPVK

-- #1013 stack probes follow Cranelift's `enable_probestack` (`Backend.StackProbe`): the prologue
-- theorems hold for any setting; without probes the facts of before the probes
-- (docs/contracts/e2e.md "Stack probes and Cranelift's settings")
#print axioms Backend.Proof.prologue_ok
#print axioms Backend.Proof.prologue_ok_off
#print axioms Backend.Proof.prologue_ok_off_witness
#print axioms Backend.probeTotal_off
#print axioms Backend.probeTotal_le
#print axioms Backend.probeCount_zero
#print axioms Backend.probeLines_zero
#print axioms Backend.prologueLines_off
#print axioms Backend.AFunc.isCaller_of_not_probes
#print axioms Backend.AFunc.isCaller_of_probes
#print axioms E2E.prologueSteps_off
#print axioms E2E.prologueSteps_of_not_probes
#print axioms E2E.probeCount_of_not_probes
#print axioms E2E.probeBelow_of_not_probes
#print axioms E2E.probeMem_of_not_probes
#print axioms E2E.probeFlag_of_not_probes
