import FV.E2E.ReturnPinBinaryKernel

namespace E2E.LiveCallBinary
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev okB := ReturnPinBinaryFor.okBFor ReturnPinAdmission.liveCalls
abbrev BinFacts := ReturnPinBinaryFor.BinFacts ReturnPinAdmission.liveCalls
abbrev okB_sound := @ReturnPinBinaryFor.okB_sound ReturnPinAdmission.liveCalls
abbrev binary_correct_depth := @ReturnPinBinaryFor.binary_correct_depth ReturnPinAdmission.liveCalls
abbrev BinFacts.modelOf_ne := @ReturnPinBinaryFor.BinFacts.modelOf_ne ReturnPinAdmission.liveCalls
abbrev binary_correct_depthX := @ReturnPinBinaryFor.binary_correct_depthX ReturnPinAdmission.liveCalls
abbrev binary_correct_peakX := @ReturnPinBinaryFor.binary_correct_peakX ReturnPinAdmission.liveCalls
abbrev binFacts_of_checks := @ReturnPinBinaryFor.binFacts_of_checks ReturnPinAdmission.liveCalls
abbrev binary_correctX := @ReturnPinBinaryFor.binary_correctX ReturnPinAdmission.liveCalls
abbrev trapsExplicit_of_run := @ReturnPinBinaryFor.trapsExplicit_of_run
abbrev trapsExplicit_of_runD := @ReturnPinBinaryFor.trapsExplicit_of_runD

end E2E.LiveCallBinary

namespace E2E.LiveCallStackBound
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev CompilerInput := SemanticStackBound.CompilerInput
abbrev okB := ReturnPinBinaryFor.okBFor ReturnPinAdmission.liveCalls
abbrev ofInput := SemanticStackBound.ofInput
abbrev okB_names := @ReturnPinStackBoundFor.okB_names ReturnPinAdmission.liveCalls
abbrev facts := @ReturnPinStackBoundFor.facts ReturnPinAdmission.liveCalls
abbrev edgeB_of_callee := @ReturnPinStackBoundFor.edgeB_of_callee ReturnPinAdmission.liveCalls
abbrev goodN_iff := @ReturnPinStackBoundFor.goodN_iff ReturnPinAdmission.liveCalls
abbrev budget_of := @ReturnPinStackBoundFor.budget_of ReturnPinAdmission.liveCalls
abbrev backend_correct_program_stackX := @ReturnPinStackBoundFor.backend_correct_program_stackX
abbrev crate_correct_stackNX := @ReturnPinStackBoundFor.crate_correct_stackNX ReturnPinAdmission.liveCalls

end E2E.LiveCallStackBound
