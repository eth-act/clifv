import FV.E2E.CallStoreAdmission
import FV.E2E.ReturnPinExecutableKernel

namespace E2E.CallStoreExecBytes
open LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev fnOk := @E2E.ReturnPinExecBytesFor.fnOk ReturnPinAdmission.callStores
abbrev codeMap_sound := @E2E.ReturnPinExecBytesFor.codeMap_sound ReturnPinAdmission.callStores
abbrev relocAt_inv := @E2E.ReturnPinExecBytesFor.relocAt_inv ReturnPinAdmission.callStores
abbrev line_overlap := @E2E.ReturnPinExecBytesFor.line_overlap ReturnPinAdmission.callStores
abbrev relocAt_img := @E2E.ReturnPinExecBytesFor.relocAt_img ReturnPinAdmission.callStores
abbrev word_static := @E2E.ReturnPinExecBytesFor.word_static ReturnPinAdmission.callStores
abbrev insn_of_good := @E2E.ReturnPinExecBytesFor.insn_of_good ReturnPinAdmission.callStores
abbrev symAddr_of_blrTo := @E2E.ReturnPinExecBytesFor.symAddr_of_blrTo ReturnPinAdmission.callStores
abbrev siteAt_static := @E2E.ReturnPinExecBytesFor.siteAt_static ReturnPinAdmission.callStores
abbrev plain_static := @E2E.ReturnPinExecBytesFor.plain_static ReturnPinAdmission.callStores
abbrev stepOk_of_d := @E2E.ReturnPinExecBytesFor.stepOk_of_d ReturnPinAdmission.callStores
abbrev runOkSN_of_n := @E2E.ReturnPinExecBytesFor.runOkSN_of_n ReturnPinAdmission.callStores
abbrev pairsClosed_art := @E2E.ReturnPinExecBytesFor.pairsClosed_art ReturnPinAdmission.callStores
abbrev raNotSecond_enter := @E2E.ReturnPinExecBytesFor.raNotSecond_enter ReturnPinAdmission.callStores
abbrev reachL_of_reachN := @E2E.ReturnPinExecBytesFor.reachL_of_reachN ReturnPinAdmission.callStores
abbrev destsInt_of_ok := @E2E.ReturnPinExecBytesFor.destsInt_of_ok
abbrev stepOkD_of_good := @E2E.ReturnPinExecBytesFor.stepOkD_of_good ReturnPinAdmission.callStores
abbrev runOkN_of_good := @E2E.ReturnPinExecBytesFor.runOkN_of_good ReturnPinAdmission.callStores
abbrev image_checked := @E2E.ReturnPinExecBytesFor.image_checked ReturnPinAdmission.callStores
abbrev extImgProduction := @E2E.LinkSys.OkReturnPins.extImgProductionFor
abbrev sysS_entry := @E2E.ReturnPinExecBytesFor.sysS_entry ReturnPinAdmission.callStores
abbrev runGood_sysS_of := @E2E.ReturnPinExecBytesFor.runGood_sysS_of ReturnPinAdmission.callStores
abbrev runGood_sysS := @E2E.ReturnPinExecBytesFor.runGood_sysS ReturnPinAdmission.callStores
abbrev runGood_sysS_depth := @E2E.ReturnPinExecBytesFor.runGood_sysS_depth ReturnPinAdmission.callStores
abbrev runGood_sysS_peak := @E2E.ReturnPinExecBytesFor.runGood_sysS_peak ReturnPinAdmission.callStores
abbrev got_of_good := @E2E.ReturnPinExecBytesFor.got_of_good ReturnPinAdmission.callStores
abbrev exec_of_runGood := @E2E.ReturnPinExecBytesFor.exec_of_runGood ReturnPinAdmission.callStores
abbrev binary_correct_exec_proven := @E2E.ReturnPinExecBytesFor.binary_correct_exec_proven ReturnPinAdmission.callStores
abbrev binary_correct_exec_depth_proven := @E2E.ReturnPinExecBytesFor.binary_correct_exec_depth_proven ReturnPinAdmission.callStores
abbrev binary_correct_exec_peak_proven := @E2E.ReturnPinExecBytesFor.binary_correct_exec_peak_proven ReturnPinAdmission.callStores

end E2E.CallStoreExecBytes
