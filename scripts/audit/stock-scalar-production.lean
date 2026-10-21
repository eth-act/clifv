import FV.E2E.StockScalarWitness
import FV.E2E.StockScalarWorldX
import FV.E2E.SemanticNIBoundary

#print axioms Backend.Stock.Proof.PureBody.actual_source_records
#print axioms Backend.Stock.Proof.PureBody.actual_pure_source_step
#print axioms Backend.Stock.Proof.PureBody.actual_pure_source_execution_frame
#print axioms Backend.Stock.Proof.PureBody.actual_pure_return_refines_at
#print axioms Backend.Stock.Proof.PureBody.actual_pure_entry_return_refines_frame
#print axioms Backend.Stock.Proof.PureBody.pure_source_notrap
#print axioms Backend.Stock.Logical.bodyEligible_sound
#print axioms Backend.Stock.Proof.LogicalBody.logical_inst_notrap
#print axioms Backend.Stock.Proof.ConstantBody.family_pure
#print axioms Backend.Stock.Proof.ConstantBody.actual_constant_families
#print axioms Backend.Stock.Proof.ConstantBody.actual_constant_body_refines
#print axioms Backend.Stock.Proof.ConstantBody.actual_constant_entry_return_refines_frame
#print axioms Backend.Stock.Proof.ConstantBody.constant_source_notrap
#print axioms Backend.Stock.Scalar.domain_of_constant
#print axioms Backend.Stock.Scalar.bodyEligible_sound
#print axioms Backend.Stock.Scalar.sourceOk_sound
#print axioms Backend.Stock.Scalar.check_sound
#print axioms E2E.backend_correct_worldX_stock_scalar
#print axioms E2E.backend_correct_world_niX_stock_scalar
#print axioms E2E.StockScalarNIWitness.checks_true -- witness: native_decide
#print axioms E2E.StockScalarNIWitness.source_checks_true -- witness: native_decide
#print axioms E2E.StockScalarNIWitness.compiled_exists -- witness: native_decide
#print axioms E2E.StockScalarNIWitness.classifier_accepts -- witness: native_decide
#print axioms E2E.StockScalarNIWitness.compiled_semantic_exists -- witness: native_decide
#print axioms E2E.StockScalarNIWitness.source_entry
#print axioms E2E.StockScalarNIWitness.source_returns

#print axioms E2E.ABIReadBoundary.checked_step_frame
#print axioms E2E.ABIReadBoundary.checked_step_transport
#print axioms E2E.ABIReadBoundary.star_transport
#print axioms E2E.ABIReadBoundary.return_transport
#print axioms E2E.ABIReadBoundary.Realize.step_realize
#print axioms E2E.ABIReadBoundary.Realize.star_realize
#print axioms E2E.ABIReadBoundary.Realize.return_realize
#print axioms E2E.ABIReadBoundary.machine_return
#print axioms E2E.MixedFlagBoundary.FlagFrame.refl
#print axioms E2E.MixedFlagBoundary.FlagFrame.write_pstate
#print axioms E2E.MixedFlagBoundary.FlagFrame.trans
#print axioms E2E.MixedFlagBoundary.FlagFrame.regVal
#print axioms E2E.MixedFlagBoundary.FlagFrame.arguments
#print axioms E2E.ScalarBoundary.refines
#print axioms E2E.ScalarBoundary.memory
#print axioms E2E.ScalarBoundary.driver
#print axioms E2E.ScalarBoundary.checked_step_frame
#print axioms E2E.ScalarBoundary.checked_step_transport
#print axioms E2E.ScalarBoundary.Realize.step_realize
#print axioms E2E.ScalarBoundary.return_transport
#print axioms E2E.ScalarBoundary.machine_return
#print axioms E2E.ScalarBoundary.checked_instruction
#print axioms E2E.CompiledSemanticNI.noTlsScalar
