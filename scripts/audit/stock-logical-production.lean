import FV.Backend.Proof.StockLogicalCheckWitness
import FV.E2E.StockLogicalWitness
import FV.E2E.SemanticLogicalCompilerWitness
import FV.E2E.SemanticRoutesWitness
import FV.E2E.StockLogicalWorldX

#print axioms E2E.backend_correct_worldX_stock_logical
#print axioms E2E.backend_correct_world_niX_stock_logical
#print axioms E2E.StockLogicalNIWitness.checks_true -- witness: native_decide
#print axioms E2E.StockLogicalNIWitness.source_checks_true -- witness: native_decide
#print axioms E2E.StockLogicalNIWitness.compiled_exists -- witness: native_decide
#print axioms E2E.StockLogicalNIWitness.source_entry
#print axioms E2E.StockLogicalNIWitness.source_returns
#print axioms E2E.StockLogicalNIWitness.classifier_accepts -- witness: native_decide
#print axioms E2E.StockLogicalNIWitness.compiled_semantic_exists -- witness: native_decide
#print axioms E2E.SemanticLogicalCompilerWitness.checks_true -- witness: native_decide
#print axioms E2E.SemanticLogicalCompilerWitness.compiler_success -- witness: native_decide
#print axioms E2E.SemanticRoutesWitness.checks_true -- witness: native_decide
#print axioms Link.SemanticCompilerWith.compileWithRoutes_accepts_tail
#print axioms Link.SemanticCompilerWith.compileWithRoutes_accepts_legacy
#print axioms Link.SemanticCompilerWith.compileWithRoutes_spec

#print axioms Backend.Stock.Proof.LogicalSelected.logical_register_source_dominated

#print axioms Backend.Stock.Logical.classifier_accepts
