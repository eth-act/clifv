import FV.Backend.Proof.StockAcquirePositionedSourceTrap
import FV.Backend.Proof.StockAcquirePositionedSourceMemory
import FV.Backend.Proof.StockAcquireSelectedSourceEndpoints
import FV.Backend.Proof.StockAcquireConsumerBodyPosition
import FV.Backend.Proof.StockAcquireSelectedSameBlock
import FV.Backend.Proof.StockAcquireActualBlockColors
import FV.Backend.Proof.StockAcquireActualTrappedSliceMemory
import FV.Backend.Proof.StockAcquireActualSourceSliceMemory
import FV.Backend.Proof.StockAcquireSelectedIntervalMemory
import FV.Backend.Proof.StockAcquireScanColorGap
import FV.Backend.Proof.StockAcquireSelectedOutputColor
import FV.Backend.Proof.StockAcquireActualReadQueueCut
import FV.Backend.Proof.StockAcquireReadIntervalCoverage
import FV.Backend.Proof.StockAcquireReadMarked
import FV.Backend.Proof.StockAcquireBranchMarkFrame
import FV.Backend.Proof.StockAcquireOutgoingMarkFrame
import FV.Backend.Proof.StockAcquireCoreMarkFrame
import FV.Backend.Proof.StockAcquireActualSourceView
import FV.Backend.Proof.StockAcquireActualCoreReadMarked
import FV.Backend.Proof.StockAcquireNodeMarkOrigin
import FV.Backend.Proof.StockAcquireDriverReadMarked
import FV.Backend.Proof.StockAcquireAllReadMarked
import FV.Backend.Proof.StockAcquirePriorReadFrontier
import FV.Backend.Proof.StockAcquireMarkReadProvenance
import FV.Backend.Proof.StockAcquireReadPendingMarks
import FV.Backend.Proof.StockAcquireReadPendingCtor
import FV.Backend.Proof.StockAcquireReadPendingRhs
import FV.Backend.Proof.StockAcquireReadPendingInterpreter
import FV.Backend.Proof.StockAcquireReadPendingNamed
import FV.Backend.Proof.StockAcquireReadPendingRecord
import FV.Backend.Proof.StockAcquireReadScanFrontiers
import FV.Backend.Proof.StockAcquireDeferredLoadPattern
import FV.Backend.Proof.StockAcquireDeferredLoadRootPattern
import FV.Backend.Proof.StockAcquireEligibilityReadSources
import FV.Backend.Proof.StockAcquireReadFormats
import FV.Backend.Proof.StockAcquireSinkFormatSources
import FV.Backend.Proof.StockAcquireSinkFormatContext
import FV.Backend.Proof.StockAcquireSinkSourceMemory
import FV.Backend.Proof.StockAcquireSinkFormatNode
import FV.Backend.Proof.StockAcquireSinkFormatDriver
import FV.Backend.Proof.StockAcquireMatchedSinkSources
import FV.Backend.Proof.StockAcquireSourceRead
import FV.Backend.Proof.StockAcquireSourceFault
import FV.Backend.Proof.StockAcquireRecordPendingOrder
import FV.Backend.Proof.StockAcquirePendingSourcePositions
import FV.Backend.Proof.StockAcquireRecordSourceInterval
import FV.Backend.Proof.StockAcquireRecordFrontier
import FV.Backend.Proof.StockAcquireScanFrontiers
import FV.Backend.Proof.StockAcquireForwardFrontiers
import FV.Backend.Proof.StockAcquireActualScanSources
import FV.Backend.Proof.StockAcquireWholeScanQueue
import FV.Backend.Proof.StockAcquireOpportunisticMarks
import FV.Backend.Proof.StockAcquireScanAssembly
import FV.Backend.Proof.StockAcquireActualScanMarks
import FV.Backend.Proof.StockAcquirePendingMarks
import FV.Backend.Proof.StockAcquirePendingMarksFrame
import FV.Backend.Proof.StockAcquirePendingMarksTrace
import FV.Backend.Proof.StockAcquirePendingBindFrame
import FV.Backend.Proof.StockAcquirePendingRecordMarks
import FV.Backend.Proof.StockAcquireSourcePointerFrame
import FV.Backend.Proof.StockAcquireOriginalPrefixPointer
import FV.Backend.Proof.StockAcquireOriginalStatement
import FV.Backend.Proof.StockAcquireRootSourceValue
import FV.Backend.Proof.StockAcquireOriginalProducer
import FV.Backend.Proof.StockAcquirePointerAvailable
import FV.Backend.Proof.StockAcquireSelectedOriginalPointerRequest
import FV.Backend.Proof.StockAcquireGuardedPointerValue
import FV.Backend.Proof.StockAcquireSinkAddress
import FV.Backend.Proof.StockAcquireSinkRequest
import FV.Backend.Proof.StockAcquireSinkCallRequest
import FV.Backend.Proof.StockAcquireOriginalPointer
import FV.Backend.Proof.StockAcquireOriginalRequest
import FV.Backend.Proof.StockAcquireSelectedPointerRequest
import FV.Backend.Proof.StockAcquireSelectedPointerValue
import FV.Backend.Proof.StockAcquireTargetWidth
import FV.Backend.Proof.StockAcquireSelectedTargetWidth
import FV.Backend.Proof.StockAcquireSelectedPairValue
import FV.Backend.Proof.StockAcquirePendingSourceOrder
import FV.Backend.Proof.StockAcquireRecordSourceOrder
import FV.Backend.Proof.StockAcquireEventOrder
import FV.Backend.Proof.StockAcquireSourceEvents
import FV.Backend.Proof.StockAcquireGlobalEventOrder
import FV.Backend.Proof.StockAcquireSourceEventIdentity
import FV.Backend.Proof.StockAcquireMetadataEvents
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

#print axioms Backend.Stock.Proof.Acquire810.body_color_events_fold
#print axioms Backend.Stock.Proof.Acquire810.block_color_events_fold
#print axioms Backend.Stock.Proof.Acquire810.source_color_events_fold
#print axioms Backend.Stock.Proof.Acquire810.sourceMetadata_color_events
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_color_events

#print axioms Backend.Stock.Proof.Acquire810.color_events_count
#print axioms Backend.Stock.Proof.Acquire810.color_events_size
#print axioms Backend.Stock.Proof.Acquire810.color_events_keeps_slot
#print axioms Backend.Stock.Proof.Acquire810.color_event_exact
#print axioms Backend.Stock.Proof.Acquire810.color_event_pair_order
#print axioms Backend.Stock.Proof.Acquire810.body_color_events_member
#print axioms Backend.Stock.Proof.Acquire810.body_color_events_bounds
#print axioms Backend.Stock.Proof.Acquire810.body_color_events_order
#print axioms Backend.Stock.Proof.Acquire810.block_color_events_member
#print axioms Backend.Stock.Proof.Acquire810.block_layout_before
#print axioms Backend.Stock.Proof.Acquire810.source_blocks_index_order
#print axioms Backend.Stock.Proof.Acquire810.block_color_event_bounds
#print axioms Backend.Stock.Proof.Acquire810.block_color_event_order
#print axioms Backend.Stock.Proof.Acquire810.source_color_event_order
#print axioms Backend.Stock.Proof.Acquire810.source_color_event_inside
#print axioms Backend.Stock.Proof.Acquire810.source_color_event_no_overwrite
#print axioms Backend.Stock.Proof.Acquire810.source_color_event_exact
#print axioms Backend.Stock.Proof.Acquire810.source_color_event_pair_exact

#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.member_positive
#print axioms Backend.Stock.Proof.Acquire810.source_color_positive_member
#print axioms Backend.Stock.Proof.Acquire810.source_color_order_reflects_slots
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.source_members
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.source_order
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_pending_source_members
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_source_order

#print axioms Backend.Stock.Proof.Acquire810.acquire_root_match_target_width
#print axioms Backend.Stock.Proof.Acquire810.acquire_root_source_target_width
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_target_width
#print axioms Backend.Stock.Proof.Acquire810.acquire_selected_pair_run

#print axioms Backend.Stock.Proof.Acquire810.sink_atomic_match_address
#print axioms Backend.Stock.Proof.Acquire810.sink_atomic_rhs_request
#print axioms Backend.Stock.Proof.Acquire810.sink_atomic_call_request
#print axioms Backend.Stock.Proof.Acquire810.mapped_atomic_original_fields
#print axioms Backend.Stock.Proof.Acquire810.sink_atomic_original_request
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_pointer_request
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_pointer_demanded
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_pointer_held

#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_original_definition
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_original_statement
#print axioms Backend.Stock.Proof.Acquire810.acquire_root_args_value
#print axioms Backend.Stock.Proof.Acquire810.acquire_root_args_value_data
#print axioms Backend.Stock.Proof.Acquire810.acquire_original_extension_data
#print axioms Backend.Stock.Proof.Acquire810.acquire_root_match_original_value
#print axioms Backend.Stock.Proof.Acquire810.acquire_rule_original_extension_source
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_pointer_available
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_original_pointer_request
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_original_pointer_demanded
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_guarded_pointer_held

#print axioms Backend.Stock.Proof.Acquire810.source_inst_pointer_frame
#print axioms Backend.Stock.Proof.Acquire810.source_steps_pointer_frame
#print axioms Backend.Stock.Proof.Acquire810.available_pointer_unwritten
#print axioms Backend.Stock.Proof.Acquire810.available_source_prefix_pointer
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_original_prefix_pointer

#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.forget
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.append
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.entryColors
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.sunk_exact
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.sunk_size
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.marked_mono
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.ordered
#print axioms Backend.Stock.Proof.Acquire810.stock_ctor_sunk_without_sink_shape
#print axioms Backend.Stock.Proof.Acquire810.stock_ctor_pending_marks_execution
#print axioms Backend.Stock.Proof.Acquire810.stock_apply_pending_marks_execution
#print axioms Backend.Stock.Proof.Acquire810.stock_runTerm_pending_marks_execution
#print axioms Backend.Stock.Proof.Acquire810.PendingMarksExecution.forget
#print axioms Backend.Stock.Proof.Acquire810.bindResults_mark_fields
#print axioms Backend.Stock.Proof.Acquire810.scanState_sunk
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_pending_marks
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_pending_mark_sources

#print axioms Backend.Stock.Proof.Acquire810.opportunisticValues_sunk
#print axioms Backend.Stock.Proof.Acquire810.opportunistic_sunk
#print axioms Backend.Stock.Proof.Acquire810.scans_forward_chunks
#print axioms Backend.Stock.Proof.Acquire810.scanBlock_forward_chunks
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_scan_run
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_all_sunk_updates
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_sunk_updates

#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_all_source_sunk_updates
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_source_sunk_updates
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_source_queue

#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_frontier
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_record_frontiers
#print axioms Backend.Stock.Proof.Acquire810.RecordFrontiers.append
#print axioms Backend.Stock.Proof.Acquire810.RecordFrontiers.reverse
#print axioms Backend.Stock.Proof.Acquire810.RecordFrontiers.source_members
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_forward_frontiers

#print axioms Backend.Stock.Proof.Acquire810.atomic_source_step_read
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_source_read
#print axioms Backend.Stock.Proof.Acquire810.atomic_source_eval_trap
#print axioms Backend.Stock.Proof.Acquire810.indexed_source_atomic_trap
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.color_some
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.nonempty_color_some
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_pending_marks_order
#print axioms Backend.Stock.Proof.Acquire810.source_color_event_lookup
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.color_at_split
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.source_event_at_split
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_pending_source_interval

#print axioms Backend.Stock.Proof.Acquire810.instData_read_format
#print axioms Backend.Stock.Proof.Acquire810.buildCtx_sink_format_sources
#print axioms Backend.Stock.Proof.Acquire810.SinkFormatSources.termCtx
#print axioms Backend.Stock.Proof.Acquire810.SinkFormatSources.withTryRegs
#print axioms Backend.Stock.Proof.Acquire810.blockCore_scan_sink_format_sources
#print axioms Backend.Stock.Proof.Acquire810.sink_format_eval_memory
#print axioms Backend.Stock.Proof.Acquire810.sink_format_source_step_memory
#print axioms Backend.Stock.Proof.Acquire810.lowerNode_sink_format_sources
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_sink_format_sources
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_sink_format_source_memory
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_pattern_sink_source_memory

#print axioms Backend.Stock.Proof.Acquire810.deferred_load_bound_source
#print axioms Backend.Stock.Proof.Acquire810.deferred_load_root_args
#print axioms Backend.Stock.Proof.Acquire810.deferred_load_rule_source
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_eligibility_sink_source_memory

#print axioms Backend.Stock.Proof.Acquire810.ReadPendingMarks.forget
#print axioms Backend.Stock.Proof.Acquire810.ReadPendingMarks.append
#print axioms Backend.Stock.Proof.Acquire810.ReadPendingMarks.source_memory
#print axioms Backend.Stock.Proof.Acquire810.ReadPendingExecution.refl
#print axioms Backend.Stock.Proof.Acquire810.ReadPendingExecution.trans
#print axioms Backend.Stock.Proof.Acquire810.stock_ctor_free_read_frame
#print axioms Backend.Stock.Proof.Acquire810.pattern_sink_read_target
#print axioms Backend.Stock.Proof.Acquire810.eligibility_sink_read_target
#print axioms Backend.Stock.Proof.Acquire810.sink_expr_read_pending
#print axioms Backend.Stock.Proof.Acquire810.sink_let_read_pending
#print axioms Backend.Stock.Proof.Acquire810.pattern_sink_rule_read_pending
#print axioms Backend.Stock.Proof.Acquire810.eligibility_sink_rule_read_pending
#print axioms Backend.Stock.Proof.Acquire810.read_pending_interpreter_frames
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_helper_read_pending
#print axioms Backend.Stock.Proof.Acquire810.stock_branch_helper_read_pending
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_read_pending_marks
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_read_pending_interval
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_read_frontier
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_read_frontiers

#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.record_prefix
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.read_frontier_groups
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_prior_read_frontier
#print axioms Backend.Stock.Proof.Acquire810.sunk_fold_absent
#print axioms Backend.Stock.Proof.Acquire810.sunk_fold_marked
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_marked_read_provenance
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_marked_read_or_entry

#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.color_covered
#print axioms Backend.Stock.Proof.Acquire810.source_color_equal_slots
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.source_interval_member
#print axioms Backend.Stock.Proof.Acquire810.ReadPendingMarks.source_interval_frame
#print axioms Backend.Stock.Proof.Acquire810.SourceReadFrame.of_source_view
#print axioms Backend.Stock.Proof.Acquire810.source_slots_termCtx
#print axioms Backend.Stock.Proof.Acquire810.SourceSlotsPreserved.withTryRegs
#print axioms Backend.Stock.Proof.Acquire810.buildCtx_read_marked
#print axioms Backend.Stock.Proof.Acquire810.ReadMarked.of_sunk_eq
#print axioms Backend.Stock.Proof.Acquire810.ReadPendingMarks.preserves_read_marked
#print axioms Backend.Stock.Proof.Acquire810.PendingMarks.none_empty
#print axioms Backend.Stock.Proof.Acquire810.stock_runTerm_none_sunk
#print axioms Backend.Stock.Proof.Acquire810.emitBranch_sunk
#print axioms Backend.Stock.Proof.Acquire810.outgoingStep_sunk
#print axioms Backend.Stock.Proof.Acquire810.collectOutgoing_sunk
#print axioms Backend.Stock.Proof.Acquire810.blockCore_scan_input_sunk
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_original_slots
#print axioms Backend.Stock.Proof.Acquire810.ReadMarked.of_read_fold
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_scan_read_marked
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_actual_core_read_marked
#print axioms Backend.Stock.Proof.Acquire810.lowerNode_mark_origin
#print axioms Backend.Stock.Proof.Acquire810.lowerNode_blockScans_keep
#print axioms Backend.Stock.Proof.Acquire810.lowerNodes_blockScans_keep
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_actual_node_read_marked
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_actual_nodes_read_marked
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_all_read_marked
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_marked_source_read

#print axioms Backend.Stock.Proof.Acquire810.ReadQueueCut.zero
#print axioms Backend.Stock.Proof.Acquire810.ReadQueueCut.of_color_eq
#print axioms Backend.Stock.Proof.Acquire810.ReadQueueCut.shrink
#print axioms Backend.Stock.Proof.Acquire810.ReadQueueCut.append_execution
#print axioms Backend.Stock.Proof.Acquire810.ReadQueueCut.reset_execution
#print axioms Backend.Stock.Proof.Acquire810.ReadQueueCut.source_read
#print axioms Backend.Stock.Proof.Acquire810.source_slot_colors_order
#print axioms Backend.Stock.Proof.Acquire810.source_metadata_positive_order
#print axioms Backend.Stock.Proof.Acquire810.referenceCut_tail_bound
#print axioms Backend.Stock.Proof.Acquire810.source_event_tail_bound
#print axioms Backend.Stock.Proof.Acquire810.scan_indices_head
#print axioms Backend.Stock.Proof.Acquire810.scan_indices_bounds
#print axioms Backend.Stock.Proof.Acquire810.scan_indices_reverse_order
#print axioms Backend.Stock.Proof.Acquire810.opportunisticValues_color_fields
#print axioms Backend.Stock.Proof.Acquire810.opportunistic_color_fields
#print axioms Backend.Stock.Proof.Acquire810.scanState_entry_colors
#print axioms Backend.Stock.Proof.Acquire810.scanState_color_zero
#print axioms Backend.Stock.Proof.Acquire810.scanState_color_positive
#print axioms Backend.Stock.Proof.Acquire810.scan_no_emission_color
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.record_run
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_read_queue_step
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_cut_source
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.cons_inv
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.read_queue_progress
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.nil_inv
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.read_queue_from_term
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_scan_prefix_read_queue_cut
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_read_queue_cut

#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.record_indices
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.record_output_prefix
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_output_read_queue_cut
#print axioms Backend.Stock.Proof.Acquire810.referenceCut_fold_above
#print axioms Backend.Stock.Proof.Acquire810.source_reference_fold_above
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_indices_reverse
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_prefix_cut_above
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_crossed_source_reads
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_output_color

#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.zero
#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.at_color
#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.of_color_eq
#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.shrink
#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.append_execution
#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.reset_execution
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_source_color_gap
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.source_color_gap_progress
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.source_color_gap_from_term
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_scan_prefix_source_color_gap
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_output_source_color_gap

#print axioms Backend.Stock.Proof.Acquire810.uncolored_source_read_frame
#print axioms Backend.Stock.Proof.Acquire810.source_steps_read_memory
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_output_source_color
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_between_source_read_frames
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_build_source_slots
#print axioms Backend.Stock.Proof.Acquire810.original_colored_statement_event
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_between_statement_read_frames
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_successful_interval_memory

#print axioms Backend.Stock.Proof.Acquire810.bare_source_statement_step
#print axioms Backend.Stock.Proof.Acquire810.bare_source_next_result
#print axioms Backend.Stock.Proof.Acquire810.bare_returned_source_slice
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_actual_successful_slice_memory

#print axioms Backend.Stock.Proof.Acquire810.source_first_trap_read_memory
#print axioms Backend.Stock.Proof.Acquire810.bare_trapped_source_slice
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_actual_trapped_slice_memory

#print axioms Backend.Stock.Proof.Acquire810.source_color_event_nonzero
#print axioms Backend.Stock.Proof.Acquire810.ColorUpperBound.of_color_eq
#print axioms Backend.Stock.Proof.Acquire810.ColorUpperBound.at_color
#print axioms Backend.Stock.Proof.Acquire810.PendingSinks.color_upper_bound
#print axioms Backend.Stock.Proof.Acquire810.scanState_color_upper_bound
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_color_upper_bound
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.color_upper_progress
#print axioms Backend.Stock.Proof.Acquire810.ScansSpec.color_upper_from_term
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_nonempty_prefix_color_upper
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_output_color_upper
#print axioms Backend.Stock.Proof.Acquire810.source_block_event_split
#print axioms Backend.Stock.Proof.Acquire810.source_block_boundary_lookup
#print axioms Backend.Stock.Proof.Acquire810.source_block_terminal_color
#print axioms Backend.Stock.Proof.Acquire810.source_block_prefix_slots
#print axioms Backend.Stock.Proof.Acquire810.source_slot_color_above_block_boundary
#print axioms Backend.Stock.Proof.Acquire810.SourceColorGap.above_block_boundary
#print axioms Backend.Stock.Proof.Acquire810.source_reference_fold_above_block_boundary
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_prefix_cut_above_boundary
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_output_block_colors
#print axioms Backend.Stock.Proof.Acquire810.source_event_same_block_of_color

#print axioms Backend.Stock.Proof.Acquire810.termCtx_source_none
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_event_term_source_none
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_producer_block

#print axioms Backend.Stock.Proof.Acquire810.acquire_root_args_unary_data
#print axioms Backend.Stock.Proof.Acquire810.ret_trap_data_not_unary
#print axioms Backend.Stock.Proof.Acquire810.stock_lowerNode_newBlockScan_prepared
#print axioms Backend.Stock.Proof.Acquire810.stock_lowerNodes_newBlockScan_prepared
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_blockScanOrigin_prepared
#print axioms Backend.Stock.Proof.Acquire810.blockCore_source_branch
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_source_slot
#print axioms Backend.Stock.Proof.Acquire810.scan_emitted_nonbranch
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_consumer_unary_data
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_consumer_source
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_consumer_body_position

#print axioms Backend.Stock.Proof.Acquire810.source_block_terminal_unique
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_block_positions
#print axioms Backend.Stock.Proof.Acquire810.acquire_root_args_original_operand_data
#print axioms Backend.Stock.Proof.Acquire810.acquire_args_original_extension
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_original_pair
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_atomic_color_position
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_selected_source_endpoints

#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_original_definition_color
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_record_original_interval_frames
#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_positioned_source_memory

#print axioms Backend.Stock.Proof.Acquire810.stock_lower_acquire_positioned_source_trap
