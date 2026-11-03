import FV.E2E.CallStoreAdmission
import FV.E2E.ReturnPinBinaryKernel

namespace E2E.CallStoreBinary
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev okB := ReturnPinBinaryFor.okBFor ReturnPinAdmission.callStores
abbrev BinFacts := ReturnPinBinaryFor.BinFacts ReturnPinAdmission.callStores
abbrev okB_sound := @ReturnPinBinaryFor.okB_sound ReturnPinAdmission.callStores
abbrev binary_correct_depth := @ReturnPinBinaryFor.binary_correct_depth ReturnPinAdmission.callStores
abbrev BinFacts.modelOf_ne := @ReturnPinBinaryFor.BinFacts.modelOf_ne ReturnPinAdmission.callStores
abbrev binary_correct_depthX := @ReturnPinBinaryFor.binary_correct_depthX ReturnPinAdmission.callStores
abbrev binary_correct_peakX := @ReturnPinBinaryFor.binary_correct_peakX ReturnPinAdmission.callStores
abbrev binFacts_of_checks := @ReturnPinBinaryFor.binFacts_of_checks ReturnPinAdmission.callStores
abbrev binary_correctX := @ReturnPinBinaryFor.binary_correctX ReturnPinAdmission.callStores
abbrev trapsExplicit_of_run := @ReturnPinBinaryFor.trapsExplicit_of_run
abbrev trapsExplicit_of_runD := @ReturnPinBinaryFor.trapsExplicit_of_runD

end E2E.CallStoreBinary

namespace E2E.CallStoreStackBound
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev CompilerInput := SemanticStackBound.CompilerInput
abbrev okB := ReturnPinBinaryFor.okBFor ReturnPinAdmission.callStores
abbrev ofInput := SemanticStackBound.ofInput
abbrev okB_names := @ReturnPinStackBoundFor.okB_names ReturnPinAdmission.callStores
abbrev facts := @ReturnPinStackBoundFor.facts ReturnPinAdmission.callStores
abbrev edgeB_of_callee := @ReturnPinStackBoundFor.edgeB_of_callee ReturnPinAdmission.callStores
abbrev goodN_iff := @ReturnPinStackBoundFor.goodN_iff ReturnPinAdmission.callStores
abbrev budget_of := @ReturnPinStackBoundFor.budget_of ReturnPinAdmission.callStores
abbrev backend_correct_program_stackX := @ReturnPinStackBoundFor.backend_correct_program_stackX
abbrev crate_correct_stackNX := @ReturnPinStackBoundFor.crate_correct_stackNX ReturnPinAdmission.callStores

end E2E.CallStoreStackBound
