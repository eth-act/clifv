import FV.Backend.Proof.SretStableX
import FV.Backend.Proof.LowerSimUAbi
import FV.E2E.SretReturnUnwind
import FV.E2E.SretReturnUnwindWitness

#print axioms Backend.Proof.Driver.sretStableX_of
#print axioms Backend.Proof.Driver.stOkX_step
#print axioms Backend.Proof.Driver.stOkX_stepX
#print axioms Backend.Proof.Driver.stOkX_reach
#print axioms Backend.Proof.Driver.sret_reachX
#print axioms Backend.Proof.Driver.runLoopX_returned_tys_entry
#print axioms Backend.Proof.Driver.RunOkUAbi.runOkU
#print axioms Backend.Proof.Driver.sim_runX_abi
#print axioms Backend.Proof.Driver.driver_correctU_abi
#print axioms E2E.iselSimUAbi_of_driver
#print axioms E2E.iselSimU_final_abi
#print axioms E2E.ArmRefinesUAbi.armRefinesU
#print axioms E2E.backend_correct_of_layersU_ex_abi
#print axioms E2E.backend_correct_final_unwind_ex_abi
#print axioms E2E.backend_correct_final_unwind_abi
#print axioms E2E.backend_correct_final_unwind_sret
#print axioms E2E.SretReturnUnwindWitness.checks_true -- witness: native_decide
#print axioms E2E.SretReturnUnwindWitness.compiled_exists -- witness: native_decide
#print axioms E2E.SretReturnUnwindWitness.sw_returns_sret_unwind -- witness: native_decide
