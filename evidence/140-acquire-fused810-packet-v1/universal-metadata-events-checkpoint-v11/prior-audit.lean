import FV.Backend.Proof.StockAcquireMetadataOrder
import FV.Backend.Proof.StockAcquireRulePendingSource
import FV.Backend.Proof.StockAcquireSelectedSingleton
import FV.Backend.Proof.StockAcquireSinkPending
import FV.Backend.Proof.StockAcquireSinkCallPending
import FV.Backend.Proof.StockAcquireRhsPending
import FV.Backend.Proof.StockAcquirePendingOrder
import FV.Backend.Proof.StockAcquirePendingFrame
import FV.Backend.Proof.StockAcquirePendingTrace
import FV.Backend.Proof.StockAcquireSelectedPending
import FV.Backend.Proof.StockAcquireDeferredSource
import FV.Backend.Proof.StockAcquireSelectedBinding
import FV.Backend.Proof.StockAcquireColorSegment
import FV.Backend.Proof.StockAcquireValueAllWidths
import FV.Backend.Proof.StockAcquireMatchSource
import FV.Backend.Proof.StockAcquireSinkForward
import FV.Backend.Proof.StockAcquireRootForward
import FV.Backend.Proof.StockAcquireSinkReceipts
import FV.Backend.Proof.StockAcquireRhsReceipts
import FV.Backend.Proof.StockAcquireRuleProvenance
import FV.Backend.Proof.StockAcquirePatternData
import FV.Backend.Proof.StockAcquireRuleSource
import FV.Backend.Proof.StockAcquireAllWidthsBinding

#print axioms Backend.Stock.Proof.Acquire810.body_color_count
#print axioms Backend.Stock.Proof.Acquire810.body_unchanged_color_quiet
#print axioms Backend.Stock.Proof.Acquire810.acquire_widened_value
#print axioms Backend.Stock.Proof.Acquire810.acquire_iflet_source
#print axioms Backend.Stock.Proof.Acquire810.acquire_root_match_source
#print axioms Backend.Stock.Proof.AcquireHelpers.sink_atomic_forward
#print axioms Backend.Stock.Proof.AcquireHelpers.output_reg_forward
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_rhs_forward
#print axioms Backend.Stock.Proof.AcquireHelpers.sink_atomic_call_receipt
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_rhs_sink_execution
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_rhs_inputs
#print axioms Backend.Stock.Proof.Acquire810.acquire_rule_sink_provenance
#print axioms Backend.Stock.Proof.AcquireHelpers.sink_atomic_match_data
#print axioms Backend.Stock.Proof.AcquireHelpers.mapped_atomic_producer
#print axioms Backend.Stock.Proof.AcquireHelpers.sink_atomic_call_data
#print axioms Backend.Stock.Proof.Acquire810.acquire_rule_original_source
#print axioms Backend.Stock.Proof.Acquire810.acquire_pair_run
#print axioms Backend.Stock.Proof.Acquire810.acquire_emission_binding
#print axioms Backend.Stock.Proof.Acquire810.acquire_record_binding
#print axioms Backend.Stock.Proof.Acquire810.acquire_record_final_binding

#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_rhs_output
#print axioms Backend.Stock.Proof.Acquire810.acquire_selected_rule
#print axioms Backend.Stock.Proof.Acquire810.acquire_selected_final_binding

#print axioms Backend.Stock.Proof.Acquire810.acquire_quiet_source_outcome
#print axioms Backend.Stock.Proof.Acquire810.acquire_quiet_source_step
#print axioms Backend.Stock.Proof.Acquire810.acquire_color_interval_source

#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.entryColors
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.color_distance
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.member_color_bounds
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.ordered
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.distinct
#print axioms Backend.Stock.Proof.Acquire810.stock_ctor_color_without_sink
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.append
#print axioms Backend.Stock.Proof.Acquire810.stock_ctor_pending_execution
#print axioms Backend.Stock.Proof.Acquire810.stock_apply_pending_execution
#print axioms Backend.Stock.Proof.Acquire810.stock_runTerm_pending_execution
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.finalColor
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_pending

#print axioms Backend.Stock.Proof.Acquire810.sink_atomic_rhs_pending
#print axioms Backend.Stock.Proof.Acquire810.sink_atomic_call_pending
#print axioms Backend.Stock.Proof.Acquire810.acquire_rhs_pending

#print axioms Backend.Stock.Proof.Acquire810.acquire_rule_pending_source
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_singleton

#print axioms Backend.Stock.Proof.Acquire810.body_color_size
#print axioms Backend.Stock.Proof.Acquire810.body_color_keeps_slot
#print axioms Backend.Stock.Proof.Acquire810.body_colored_exact
#print axioms Backend.Stock.Proof.Acquire810.body_colored_pair_order
