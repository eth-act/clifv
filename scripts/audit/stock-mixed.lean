import FV.E2E.StockMixedWitness
import FV.E2E.SemanticMixedCompilerWitness
import FV.E2E.SemanticFallbackWitness
import FV.Backend.MixedNIProduction

#print axioms Backend.Stock.Proof.MixedBody.actual_mixed_families
#print axioms Backend.Stock.Proof.MixedBody.actual_mixed_entry_return_refines_frame
#print axioms Backend.Stock.Proof.MixedBody.mixed_source_notrap
#print axioms Backend.Stock.Mixed.sourceOk_sound
#print axioms Backend.Stock.Mixed.check_sound
#print axioms E2E.MixedFlagBoundary.Realize.return_realize
#print axioms E2E.MixedFlagBoundary.machine_return
#print axioms E2E.backend_correct_world_niX_stock_mixed
#print axioms E2E.backend_correct_worldX_stock_mixed
#print axioms Link.SemanticCompilerWith.compileWithFallback_spec
#print axioms Link.SemanticCompilerWith.accepts_previous
#print axioms E2E.StockMixedNIWitness.source_entry
#print axioms E2E.StockMixedNIWitness.source_returns
-- witness: native_decide (fixed pipeline data)
#print axioms E2E.StockMixedNIWitness.checks_true
-- witness: native_decide (fixed source/provenance data)
#print axioms E2E.StockMixedNIWitness.source_checks_true
-- witness: native_decide (fixed allocated/emitted artifacts)
#print axioms E2E.StockMixedNIWitness.compiled_semantic_exists
-- witness: native_decide (fixed actual ELF compiler data)
#print axioms E2E.SemanticMixedCompilerWitness.checks_true
-- witness: native_decide (fixed actual fallback/compiler choices)
#print axioms E2E.SemanticFallbackWitness.checks_true
