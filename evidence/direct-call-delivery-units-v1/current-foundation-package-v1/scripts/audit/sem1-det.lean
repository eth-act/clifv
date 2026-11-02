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
