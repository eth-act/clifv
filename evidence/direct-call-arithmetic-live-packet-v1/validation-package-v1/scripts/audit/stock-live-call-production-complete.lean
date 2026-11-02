import FV.Backend.LiveCallProduction
import FV.E2E.LiveCallProductionSelection
#print axioms E2E.LiveCallProductionExec.compiler_success -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.concrete_facts -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.outside_call -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.intact -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.program_find -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.source_entry -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.clif_run -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.base_ok -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.source_returns -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.executable_witness -- witness: native_decide
#print axioms E2E.LiveCallProductionExec.returned_word -- witness: native_decide
#print axioms E2E.LiveCallProductionSelection.selected -- witness: native_decide
#print axioms E2E.LiveCallProductionSelection.actual_entrypoint -- witness: native_decide
#print axioms E2E.LiveCallProductionSelection.actual_provider -- witness: native_decide
#print axioms E2E.LiveCallProductionSelection.mixed_rejected -- witness: native_decide
#print axioms E2E.LiveCallProductionSelection.mixed_complete_retry -- witness: native_decide

#print axioms Backend.compileFileLiveCallWhen_disabled
#print axioms Backend.compileFileLiveCallWhen_retry
