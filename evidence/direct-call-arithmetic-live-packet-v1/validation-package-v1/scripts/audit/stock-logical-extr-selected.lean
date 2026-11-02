import FV.E2E.StockLogicalExtrRootWitness
set_option pp.privateNames true

#print axioms Backend.Stock.Proof.LogicalExtr.selected_root_values
-- witness: native_decide (fixed first-match calls in six ABIs and both mirror cases)
#print axioms E2E.StockLogicalExtrWitness.selected_root_values_witness -- witness: native_decide

#print axioms Backend.Stock.Proof.LogicalExtr.record_values
#print axioms Backend.Stock.Proof.LogicalExtr.available_values
#print axioms Backend.Stock.Proof.LogicalExtr.source_operands
#print axioms Backend.Stock.Proof.LogicalExtr.available_source
#print axioms Backend.Stock.Proof.LogicalExtr.source_from_step
-- witness: native_decide (fixed complete driver observations only)
#print axioms E2E.StockLogicalExtrWitness.record_values_witness -- witness: native_decide
-- witness: native_decide (fixed complete driver/pipeline observations only)
#print axioms E2E.StockLogicalExtrWitness.source_values_witness -- witness: native_decide
