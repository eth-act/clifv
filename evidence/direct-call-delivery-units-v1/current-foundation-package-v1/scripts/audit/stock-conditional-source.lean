import FV.E2E.SemanticNIBoundary
import FV.Backend.Proof.StockConditionalDomainWitness
import FV.Backend.Proof.StockConditionalTrapAtWitness
import FV.Backend.Proof.StockConditionalClassWitness
import FV.Backend.Proof.StockConditionalReturnAtWitness
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockConditionalRouteWitness
import FV.Backend.Proof.StockConditionalSourceTrapWitness
import FV.Backend.Proof.StockConditionalSourceReturnWitness
import FV.Backend.Proof.StockConditionalGuardedWitness
import FV.Backend.Proof.StockConditionalOutgoingWitness
import FV.Backend.Proof.StockConditionalDemandWitness
import FV.Backend.Proof.StockConditionalCoreOriginWitness
import FV.Backend.Proof.StockConditionPrefixWitness
import FV.Backend.Proof.StockResolvedDefsWitness
import FV.Backend.Proof.StockSequenceFrame
import FV.Backend.Proof.StockConditionalSourceValuesWitness
import FV.Backend.Proof.StockConditionalResolvedWitness
import FV.Backend.Proof.StockConditionalCallsWitness
import FV.Backend.Proof.StockConditionalEmissionWitness

#print axioms Backend.Stock.Proof.BranchHelpers.stock_emit_side_effect_projects
#print axioms Backend.Stock.Proof.Sequence.append_fall_inv
#print axioms Backend.Stock.Proof.Sequence.append_fall_inv_witness
#print axioms Backend.Stock.Proof.ConditionalCalls.selected_calls
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.source_of_slot
#print axioms Backend.Stock.Proof.ConditionalCalls.calls_witness
#print axioms Backend.Stock.Proof.ConditionalCalls.source_calls_witness
#print axioms Backend.Stock.Proof.ConditionalValues.branch_of_boolean_companion
#print axioms Backend.Stock.Proof.ConditionalValues.branch_companion_witness
#print axioms Backend.Stock.Proof.ConditionalValues.zero_branch_of_boolean_companion
#print axioms Backend.Stock.Proof.ConditionalValues.zero_branch_companion_witness
#print axioms Backend.Stock.Proof.ConditionalValues.descriptor_shape
#print axioms Backend.Stock.Proof.ConditionalValues.descriptor_emitter_witness
#print axioms Backend.Stock.Proof.ConditionalValues.descriptor_emits
#print axioms Backend.Stock.Proof.ConditionalValues.emission_witness

#print axioms Backend.Stock.Proof.ConditionalValues.nonzero_boolean_values
#print axioms Backend.Stock.Proof.ConditionalValues.original_boolean_companion
#print axioms Backend.Stock.Proof.ConditionalValues.SourceWitness.original_source_companion_witness
#print axioms Backend.Stock.Proof.ConditionalValues.SourceWitness.nonzero_source_companion_witness
#print axioms Backend.Stock.Proof.ConditionalValues.flag_branch_resolved
#print axioms Backend.Stock.Proof.ConditionalValues.zero_branch_resolved
#print axioms Backend.Stock.Proof.ConditionalValues.ResolvedWitness.flag_resolved_witness
#print axioms Backend.Stock.Proof.ConditionalValues.ResolvedWitness.zero_resolved_witness

#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_nonzero_prefix
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_nonzero_prefix_witness
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_zero_rhs_prefix
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_zero_prefix_witness
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_wide_comparison_prefix
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_narrow_comparison_prefix
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_comparison_prefix_witness
#print axioms Backend.Stock.Proof.ConditionalValues.comparison_prefix
#print axioms Backend.Stock.Proof.ConditionalValues.original_prefix
#print axioms Backend.Stock.Proof.ConditionalValues.SourceWitness.original_prefix_witness
#print axioms Backend.Stock.Proof.Resolved.renamed_defs
#print axioms Backend.Stock.Proof.Resolved.fragment_defs
#print axioms Backend.Stock.Proof.Resolved.fragment_frame
#print axioms Backend.Stock.Proof.Resolved.renamed_defs_witness
#print axioms Backend.Stock.Proof.Resolved.fragment_endpoint_witness
#print axioms Backend.Stock.Proof.Sequence.stop_frame
#print axioms Backend.Stock.Proof.Sequence.stop_frame_witness

#print axioms Backend.Stock.Proof.ConditionalValues.original_source_branch_values
#print axioms Backend.Stock.Proof.ConditionalCalls.source_calls_fixture_witness
#print axioms Backend.Stock.Proof.ConditionalValues.SourceWitness.named_source_branch_witness

#print axioms Backend.Stock.Proof.ConditionalValues.conditional_core_origin
#print axioms Backend.Stock.Proof.ConditionalValues.conditional_core_origin_witness
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.source_values

#print axioms Backend.Stock.Proof.ConditionalValues.nonzero_source_branch_values
#print axioms Backend.Stock.Proof.ConditionalValues.parameter_source_branch_values
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.parameter_source_values
#print axioms Backend.Stock.Proof.ConditionalValues.SourceWitness.parameter_frontier_branch_witness

#print axioms Backend.Stock.Proof.ConditionalValues.conditional_core_calls
#print axioms Backend.Stock.Proof.ConditionalValues.stock_lower_conditional_body_spec
#print axioms Backend.Stock.Proof.ConditionalValues.BodyWitness.executable_conditional_body_witness
#print axioms Backend.Stock.Proof.ConditionalValues.conditional_core_emission_demand
#print axioms Backend.Stock.Proof.ConditionalValues.BodyWitness.conditional_core_demand_witness

#print axioms Backend.Stock.Proof.ConditionalValues.nonzero_wide_no_defs
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.parameter_wide_no_defs
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.parameter_wide_source_values
#print axioms Backend.Stock.Proof.ConditionalValues.SourceWitness.parameter_wide_full_frame_witness
#print axioms Backend.Stock.Proof.ParameterBranch.parameter_selected
#print axioms Backend.Stock.Proof.ParameterBranch.named_calls

#print axioms Backend.Stock.Proof.outgoing_base_extent
#print axioms Backend.Stock.Proof.ConditionalValues.BodyWitness.conditional_outgoing_frame_witness
#print axioms Backend.Stock.Proof.ConditionalValues.nonzero_wide_allocation
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.parameter_wide_bounds
#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.parameter_branch_values
#print axioms Backend.Stock.Proof.ConditionalValues.GuardedWitness.executable_parameter_branch_witness

#print axioms Backend.Stock.Proof.buildCtx_term_available
#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.parameter_calls
#print axioms Backend.Stock.Proof.ConditionalValues.nonzero_wide_emitted_size
#print axioms Backend.Stock.Proof.ConditionalCalls.Calls.parameter_wide_emitted_size
#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.parameter_branch_values_last
#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.returning_parameter_core
#print axioms Backend.Stock.Proof.ConditionalValues.ReturnWitness.returning_parameter_core_witness

#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.trapping_parameter_core
#print axioms Backend.Stock.Proof.ConditionalValues.TrapFixture.driver_witness
#print axioms Backend.Stock.Proof.ConditionalValues.TrapWitness.trapping_parameter_core_witness

#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.selected_successor_guarded_of_demand
#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.selected_successor_guarded
#print axioms Backend.Stock.Proof.ConditionalValues.SuccessorWitness.selected_successor_witness
#print axioms Backend.Stock.Proof.SelectedCopyRoute.execute
#print axioms Backend.Stock.Proof.ConditionalValues.RouteWitness.selected_route_execution_witness

#print axioms Backend.Stock.Proof.Control.original_entry_prelude
#print axioms Backend.Stock.Proof.ConditionalValues.conditional_entry_prelude
#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.returning_empty_parameter_at
#print axioms Backend.Stock.Proof.ConditionalValues.EmptyFixture.driver_witness
#print axioms Backend.Stock.Proof.ConditionalValues.ReturnAtWitness.returning_empty_parameter_at_witness
#print axioms Backend.Stock.Proof.ConditionalValues.ReturnAtWitness.returning_empty_parameter_entry_witness
#print axioms Backend.Stock.Proof.Control.jump_entry_prelude
#print axioms Backend.Stock.Proof.Control.source_defined_entry_frame

#print axioms Backend.Stock.Proof.ConditionalValues.ConditionalBodySpec.trapping_empty_parameter_at
#print axioms Backend.Stock.Proof.ConditionalValues.EmptyTrapFixture.lower_success
#print axioms Backend.Stock.Proof.ConditionalValues.EmptyTrapFixture.driver_witness
#print axioms Backend.Stock.Proof.ConditionalValues.TrapAtWitness.trapping_empty_parameter_at_witness
#print axioms Backend.Stock.Proof.ConditionalValues.TrapAtWitness.trapping_empty_parameter_entry_witness
#print axioms Backend.Stock.Proof.ConditionalValues.SuccessorReturn.of_return_block
#print axioms Backend.Stock.Proof.ConditionalValues.SuccessorTrap.of_return_block
#print axioms Backend.Stock.Proof.ConditionalValues.compatible_conditional_sources_witness
#print axioms Backend.Stock.ConditionalCfg.eligible_shape
#print axioms Backend.Stock.ConditionalCfg.Shape.condition_metadata

#print axioms Backend.Stock.ConditionalCfg.Shape.legacy_compatible
#print axioms Backend.Stock.Proof.ConditionalValues.compatible_conditional_code_witness
#print axioms Backend.Stock.ConditionalCfg.domain_of_shape
#print axioms Backend.Stock.ConditionalCfg.domain_of_eligible
#print axioms Backend.Stock.ConditionalCfg.sourceOk_sound
#print axioms Backend.Stock.ConditionalCfg.check_sound
#print axioms Backend.Stock.Proof.ConditionalValues.conditional_source_checks_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.ConditionalValues.checked_conditional_driver_witness -- witness: native_decide

#print axioms E2E.CfgBoundary.checked_step_frame
#print axioms E2E.CfgBoundary.checked_step_transport
#print axioms E2E.CfgBoundary.Realize.step_realize
#print axioms E2E.CompiledSemanticNI.noTlsCfg
#print axioms E2E.CompiledSemanticNI.of_checks
