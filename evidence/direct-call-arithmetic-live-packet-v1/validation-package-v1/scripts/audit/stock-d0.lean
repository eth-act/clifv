import FV.Backend.Proof.StockD0Compiler
import FV.Backend.Proof.StockD0Source
import FV.Backend.Proof.StockD0PipelineWitness
import FV.Backend.Proof.StockD0FallbackWitness
import FV.Backend.Proof.LoweringPipeline
import FV.E2E.LoweringPipeline

#print axioms Backend.Stock.D0.erased_code
#print axioms Backend.Stock.D0.legacy_name
#print axioms Backend.Stock.D0.normalized_eq_legacy
#print axioms Backend.Stock.D0.eligible_sound
#print axioms Backend.Stock.D0.defaultLower_eq_legacy
#print axioms Backend.Stock.D0.failed_stock_falls_back
#print axioms Backend.Stock.D0.selectWith_eq_original
#print axioms Backend.Stock.D0.source_eligible
#print axioms Backend.Stock.D0.stock_succeeds
#print axioms Backend.Stock.D0.stock_edges_empty
#print axioms Backend.Stock.D0.actual_stock_dispatch
#print axioms Backend.Stock.D0.default_source_success
#print axioms Backend.Stock.D0.source_entry
#print axioms Backend.Stock.D0.source_return
#print axioms Backend.Stock.D0.dirty_machine_bits
#print axioms Backend.Stock.D0.source_memory_roundtrip
#print axioms Backend.Stock.D0.source_complete_witness
#print axioms Backend.Stock.D0.complete_pipeline_witness
#print axioms Backend.Stock.D0.forced_failure_witness
#print axioms Backend.Stock.D0.nonempty_edges_fall_back
#print axioms Backend.Stock.D0.edge_guard_witness
#print axioms Backend.Stock.D0.Compiler.lowerChecked_eq_legacy
#print axioms Backend.Stock.D0.Compiler.lowerForAllocation_eq_legacy
#print axioms Backend.Stock.D0.Compiler.compileFileWith_eq_legacy
#print axioms Backend.Stock.D0.Compiler.compiler_compatibility_witness
#print axioms Backend.Proof.LoweringPipeline.compileFileWith_legacy
#print axioms Backend.Proof.LoweringPipeline.successor_payload_witness
#print axioms Backend.Proof.LoweringPipeline.legacy_specialization_witness
#print axioms E2E.LinkCheck.LoweringPipeline.pipe_legacy
#print axioms E2E.LinkCheck.LoweringPipeline.pipeT_legacy
#print axioms E2E.LinkCheck.LoweringPipeline.pipeCleanup_legacy
#print axioms E2E.LinkCheck.LoweringPipeline.pipeCleanupT_legacy
#print axioms E2E.LinkCheck.LoweringPipeline.pipeWithLowering_congr
#print axioms E2E.LinkCheck.LoweringPipeline.pipeTWithLowering_congr
#print axioms E2E.LinkCheck.LoweringPipeline.legacy_consumer_witness
