import FV.E2E.ReturnPinBinaryKernel

namespace E2E.ResultCallBinary
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev okB := ReturnPinBinaryFor.okBFor ReturnPinAdmission.resultCalls
abbrev BinFacts := ReturnPinBinaryFor.BinFacts ReturnPinAdmission.resultCalls
abbrev okB_sound := @ReturnPinBinaryFor.okB_sound ReturnPinAdmission.resultCalls
abbrev binary_correct_depth := @ReturnPinBinaryFor.binary_correct_depth ReturnPinAdmission.resultCalls
abbrev BinFacts.modelOf_ne := @ReturnPinBinaryFor.BinFacts.modelOf_ne ReturnPinAdmission.resultCalls
abbrev binary_correct_depthX := @ReturnPinBinaryFor.binary_correct_depthX ReturnPinAdmission.resultCalls
abbrev binary_correct_peakX := @ReturnPinBinaryFor.binary_correct_peakX ReturnPinAdmission.resultCalls
abbrev binFacts_of_checks := @ReturnPinBinaryFor.binFacts_of_checks ReturnPinAdmission.resultCalls
abbrev binary_correctX := @ReturnPinBinaryFor.binary_correctX ReturnPinAdmission.resultCalls
abbrev trapsExplicit_of_run := @ReturnPinBinaryFor.trapsExplicit_of_run
abbrev trapsExplicit_of_runD := @ReturnPinBinaryFor.trapsExplicit_of_runD

end E2E.ResultCallBinary

namespace E2E.ResultCallStackBound
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev CompilerInput := SemanticStackBound.CompilerInput
abbrev okB := ReturnPinBinaryFor.okBFor ReturnPinAdmission.resultCalls
abbrev ofInput := SemanticStackBound.ofInput
abbrev okB_names := @ReturnPinStackBoundFor.okB_names ReturnPinAdmission.resultCalls
abbrev facts := @ReturnPinStackBoundFor.facts ReturnPinAdmission.resultCalls
abbrev edgeB_of_callee := @ReturnPinStackBoundFor.edgeB_of_callee ReturnPinAdmission.resultCalls
abbrev goodN_iff := @ReturnPinStackBoundFor.goodN_iff ReturnPinAdmission.resultCalls
abbrev budget_of := @ReturnPinStackBoundFor.budget_of ReturnPinAdmission.resultCalls
abbrev backend_correct_program_stackX := @ReturnPinStackBoundFor.backend_correct_program_stackX
abbrev crate_correct_stackNX := @ReturnPinStackBoundFor.crate_correct_stackNX ReturnPinAdmission.resultCalls

end E2E.ResultCallStackBound
