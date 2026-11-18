import FV.E2E.GotTab
import FV.E2E.ReturnPinExecProven
import FV.E2E.SemanticExecTS
import FV.E2E.DeadCleanupExecProvenT
import FV.E2E.DeadCleanupExecPeakT

-- #1092, #1093: the GOT premise decided on link-check's result table, and the theorems the
-- binary check names (FVTest/E2E/BinVerdict.lean)
#print axioms E2E.GotTab.ldrFormB_ldrW
#print axioms E2E.SemanticExecBytes.gotTabB_sound
#print axioms E2E.DeadCleanupExecBytes.gotTabB_sound
#print axioms E2E.ReturnPinExecBytes.binary_correct_exec_proven
#print axioms E2E.ReturnPinExecBytes.binary_correct_exec_peak_proven
#print axioms E2E.SemanticExecBytes.binary_correct_exec_provenTS
#print axioms E2E.SemanticExecBytes.binary_correct_exec_peak_provenTS
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_provenT
#print axioms E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT
