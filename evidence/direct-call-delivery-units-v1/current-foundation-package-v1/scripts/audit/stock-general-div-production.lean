import FV.E2E.StockGeneralDivWitness
import FV.Backend.Proof.StockScalarCheck
set_option pp.privateNames true
#print axioms Backend.Stock.Scalar.divisionBodyEligible_sound
#print axioms Backend.Stock.Scalar.generalDivBodyEligible_sound
#print axioms Backend.Stock.Scalar.sourceOk_sound
#print axioms Backend.Stock.Scalar.domain_of_scalar_div
#print axioms E2E.StockGeneralDivNIWitness.outcomeAgrees_sound
#print axioms E2E.StockGeneralDivNIWitness.checks_true -- witness: native_decide
#print axioms E2E.StockGeneralDivNIWitness.source_cases -- witness: native_decide
#print axioms E2E.StockGeneralDivNIWitness.compiled_exists -- witness: native_decide
#print axioms E2E.StockGeneralDivNIWitness.source_entry
