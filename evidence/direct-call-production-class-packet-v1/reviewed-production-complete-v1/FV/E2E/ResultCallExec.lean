import FV.E2E.ReturnPinExecutableKernel

namespace E2E.ResultCallExecBytes
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev fnOk := @E2E.ReturnPinExecBytesFor.fnOk ReturnPinAdmission.resultCalls
abbrev codeMap_sound := @E2E.ReturnPinExecBytesFor.codeMap_sound ReturnPinAdmission.resultCalls
abbrev relocAt_inv := @E2E.ReturnPinExecBytesFor.relocAt_inv ReturnPinAdmission.resultCalls
abbrev line_overlap := @E2E.ReturnPinExecBytesFor.line_overlap ReturnPinAdmission.resultCalls
abbrev relocAt_img := @E2E.ReturnPinExecBytesFor.relocAt_img ReturnPinAdmission.resultCalls
abbrev word_static := @E2E.ReturnPinExecBytesFor.word_static ReturnPinAdmission.resultCalls
abbrev insn_of_good := @E2E.ReturnPinExecBytesFor.insn_of_good ReturnPinAdmission.resultCalls
abbrev symAddr_of_blrTo := @E2E.ReturnPinExecBytesFor.symAddr_of_blrTo ReturnPinAdmission.resultCalls
abbrev siteAt_static := @E2E.ReturnPinExecBytesFor.siteAt_static ReturnPinAdmission.resultCalls
abbrev plain_static := @E2E.ReturnPinExecBytesFor.plain_static ReturnPinAdmission.resultCalls
abbrev stepOk_of_d := @E2E.ReturnPinExecBytesFor.stepOk_of_d ReturnPinAdmission.resultCalls
abbrev runOkSN_of_n := @E2E.ReturnPinExecBytesFor.runOkSN_of_n ReturnPinAdmission.resultCalls
abbrev pairsClosed_art := @E2E.ReturnPinExecBytesFor.pairsClosed_art ReturnPinAdmission.resultCalls
abbrev raNotSecond_enter := @E2E.ReturnPinExecBytesFor.raNotSecond_enter ReturnPinAdmission.resultCalls
abbrev reachL_of_reachN := @E2E.ReturnPinExecBytesFor.reachL_of_reachN ReturnPinAdmission.resultCalls
abbrev destsInt_of_ok := @E2E.ReturnPinExecBytesFor.destsInt_of_ok
abbrev stepOkD_of_good := @E2E.ReturnPinExecBytesFor.stepOkD_of_good ReturnPinAdmission.resultCalls
abbrev runOkN_of_good := @E2E.ReturnPinExecBytesFor.runOkN_of_good ReturnPinAdmission.resultCalls
abbrev image_checked := @E2E.ReturnPinExecBytesFor.image_checked ReturnPinAdmission.resultCalls
abbrev extImgProduction := @E2E.LinkSys.OkReturnPins.extImgProductionFor
abbrev sysS_entry := @E2E.ReturnPinExecBytesFor.sysS_entry ReturnPinAdmission.resultCalls
abbrev runGood_sysS_of := @E2E.ReturnPinExecBytesFor.runGood_sysS_of ReturnPinAdmission.resultCalls
abbrev runGood_sysS := @E2E.ReturnPinExecBytesFor.runGood_sysS ReturnPinAdmission.resultCalls
abbrev runGood_sysS_depth := @E2E.ReturnPinExecBytesFor.runGood_sysS_depth ReturnPinAdmission.resultCalls
abbrev runGood_sysS_peak := @E2E.ReturnPinExecBytesFor.runGood_sysS_peak ReturnPinAdmission.resultCalls
abbrev got_of_good := @E2E.ReturnPinExecBytesFor.got_of_good ReturnPinAdmission.resultCalls
abbrev exec_of_runGood := @E2E.ReturnPinExecBytesFor.exec_of_runGood ReturnPinAdmission.resultCalls
abbrev binary_correct_exec_proven := @E2E.ReturnPinExecBytesFor.binary_correct_exec_proven ReturnPinAdmission.resultCalls
abbrev binary_correct_exec_depth_proven := @E2E.ReturnPinExecBytesFor.binary_correct_exec_depth_proven ReturnPinAdmission.resultCalls
abbrev binary_correct_exec_peak_proven := @E2E.ReturnPinExecBytesFor.binary_correct_exec_peak_proven ReturnPinAdmission.resultCalls

end E2E.ResultCallExecBytes
