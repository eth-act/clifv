import FV.Backend.Proof.StockAddSubAllSourceValues
import FV.Backend.Proof.StockAddSubAllValues
import FV.Backend.Proof.StockAddSubAuxWitness
import FV.Backend.Proof.StockAddSubDispatch
import FV.Backend.Proof.StockAddSubExtensionWitness
import FV.Backend.Proof.StockAddSubImmediateMatch
import FV.Backend.Proof.StockAddSubImmediateValues
import FV.Backend.Proof.StockAddSubImmediateWitness
import FV.Backend.Proof.StockAddSubMatch
import FV.Backend.Proof.StockAddSubNegativeMatch
import FV.Backend.Proof.StockAddSubNegativePure
import FV.Backend.Proof.StockAddSubNegativeValues
import FV.Backend.Proof.StockAddSubNegativeWitness
import FV.Backend.Proof.StockAddSubObserved
import FV.Backend.Proof.StockAddSubPure
import FV.Backend.Proof.StockAddSubRecordValues
import FV.Backend.Proof.StockAddSubRhs
import FV.Backend.Proof.StockAddSubSelected
import FV.Backend.Proof.StockAddSubSemantics
import FV.Backend.Proof.StockAddSubShiftEdgeWitness
import FV.Backend.Proof.StockAddSubShiftWitness
import FV.Backend.Proof.StockAddSubSourceValues
import FV.Backend.Proof.StockAddSubUnifiedValues
import FV.Backend.Proof.StockAddSubValues
import FV.Backend.Proof.StockAliasAvailable
import FV.Backend.Proof.StockAliasDomain
import FV.Backend.Proof.StockAliasTerminal
import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockAluRecordValues
import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockAvailableValues
import FV.Backend.Proof.StockBitHelper
import FV.Backend.Proof.StockBitrevDispatchWitness
import FV.Backend.Proof.StockBitrevForms
import FV.Backend.Proof.StockBitrevRecordValues
import FV.Backend.Proof.StockBitrevRhs
import FV.Backend.Proof.StockBitrevSelected
import FV.Backend.Proof.StockBitrevSemantics
import FV.Backend.Proof.StockBitrevSourceValues
import FV.Backend.Proof.StockBitrevWitness
import FV.Backend.Proof.StockBnotWitness
import FV.Backend.Proof.StockBswapDispatchWitness
import FV.Backend.Proof.StockBswapRecordValues
import FV.Backend.Proof.StockBswapRhs
import FV.Backend.Proof.StockBswapSelected
import FV.Backend.Proof.StockBswapSemantics
import FV.Backend.Proof.StockBswapSourceValues
import FV.Backend.Proof.StockBswapWitness
import FV.Backend.Proof.StockCastBaseValues
import FV.Backend.Proof.StockCastNoTypeWitness
import FV.Backend.Proof.StockCastRecordValues
import FV.Backend.Proof.StockCastSourceValues
import FV.Backend.Proof.StockCastWitness
import FV.Backend.Proof.StockCmpBuilders
import FV.Backend.Proof.StockCmpCondition
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockCmpConditionWitness
import FV.Backend.Proof.StockCmpFlags
import FV.Backend.Proof.StockCmpMachineValues
import FV.Backend.Proof.StockCmpMachineWitness
import FV.Backend.Proof.StockCmpNonconstantDriverRuns
import FV.Backend.Proof.StockCmpNonconstantDriverWitness
import FV.Backend.Proof.StockCmpNonconstantRecordValues
import FV.Backend.Proof.StockCmpNonconstantRootValues
import FV.Backend.Proof.StockCmpNonconstantSelection
import FV.Backend.Proof.StockCmpNonconstantSourceValues
import FV.Backend.Proof.StockCmpNonconstantValues
import FV.Backend.Proof.StockCmpOutput
import FV.Backend.Proof.StockCmpParameterDriverRuns
import FV.Backend.Proof.StockCmpParameterDriverWitness
import FV.Backend.Proof.StockCmpParameterRecordValues
import FV.Backend.Proof.StockCmpParameterRootValues
import FV.Backend.Proof.StockCmpParameterRootWitness
import FV.Backend.Proof.StockCmpParameterSourceValues
import FV.Backend.Proof.StockCmpParameterValues
import FV.Backend.Proof.StockCmpPure
import FV.Backend.Proof.StockCmpPureWitness
import FV.Backend.Proof.StockCmpRegisterEmission
import FV.Backend.Proof.StockCmpRegisterSelection
import FV.Backend.Proof.StockCmpRegisterTraceValues
import FV.Backend.Proof.StockCmpRegisterValues
import FV.Backend.Proof.StockCmpRegisterValuesWitness
import FV.Backend.Proof.StockCmpRootMatch
import FV.Backend.Proof.StockCmpSelectedCalls
import FV.Backend.Proof.StockCmpSelectedCallsWitness
import FV.Backend.Proof.StockCmpSourceMatch
import FV.Backend.Proof.StockCmpSourceMatchWitness
import FV.Backend.Proof.StockCmpWithFlags
import FV.Backend.Proof.StockConstantRecordValues
import FV.Backend.Proof.StockCountClzNonzeroWitness
import FV.Backend.Proof.StockCountClzZeroWitness
import FV.Backend.Proof.StockCountCtzNonzeroWitness
import FV.Backend.Proof.StockCountCtzZeroWitness
import FV.Backend.Proof.StockCountForms
import FV.Backend.Proof.StockCountMath
import FV.Backend.Proof.StockCountRecordValues
import FV.Backend.Proof.StockCountRhs
import FV.Backend.Proof.StockCountSelected
import FV.Backend.Proof.StockCountSemantics
import FV.Backend.Proof.StockCountSourceValues
import FV.Backend.Proof.StockCoverageRecords
import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockDivAliasSem
import FV.Backend.Proof.StockDivBodyValueWitness
import FV.Backend.Proof.StockDivBodyValues
import FV.Backend.Proof.StockDivConstant
import FV.Backend.Proof.StockDivDispatch
import FV.Backend.Proof.StockDivDividendValueWitness
import FV.Backend.Proof.StockDivDividendValues
import FV.Backend.Proof.StockDivDivisorValueWitness
import FV.Backend.Proof.StockDivDivisorValues
import FV.Backend.Proof.StockDivFlags
import FV.Backend.Proof.StockDivGeneralValues
import FV.Backend.Proof.StockDivGuardSemantics
import FV.Backend.Proof.StockDivGuardWitness
import FV.Backend.Proof.StockDivHelperWitness
import FV.Backend.Proof.StockDivHelpers
import FV.Backend.Proof.StockDivImmFrame
import FV.Backend.Proof.StockDivImmOperandValues
import FV.Backend.Proof.StockDivImmPure
import FV.Backend.Proof.StockDivImmResolved
import FV.Backend.Proof.StockDivImmResolvedWitness
import FV.Backend.Proof.StockDivImmValues
import FV.Backend.Proof.StockDivImmWitness
import FV.Backend.Proof.StockDivIntmin
import FV.Backend.Proof.StockDivLcf
import FV.Backend.Proof.StockDivMatch
import FV.Backend.Proof.StockDivMinimumResolved
import FV.Backend.Proof.StockDivMinimumWitness
import FV.Backend.Proof.StockDivMovK
import FV.Backend.Proof.StockDivObservations
import FV.Backend.Proof.StockDivPure
import FV.Backend.Proof.StockDivRecordReceiptWitness
import FV.Backend.Proof.StockDivRecordReceipts
import FV.Backend.Proof.StockDivRemNarrowRecordValues
import FV.Backend.Proof.StockDivRemNarrowSourceValues
import FV.Backend.Proof.StockDivRemNarrowValues
import FV.Backend.Proof.StockDivRemSelectedWitness
import FV.Backend.Proof.StockDivRemValues
import FV.Backend.Proof.StockDivRemWideRecordValues
import FV.Backend.Proof.StockDivRemWideSourceValues
import FV.Backend.Proof.StockDivRemWideValues
import FV.Backend.Proof.StockDivRequestWitness
import FV.Backend.Proof.StockDivRequests
import FV.Backend.Proof.StockDivResolved
import FV.Backend.Proof.StockDivResolvedGuardWitness
import FV.Backend.Proof.StockDivResolvedGuards
import FV.Backend.Proof.StockDivResolvedWitness
import FV.Backend.Proof.StockDivRhs
import FV.Backend.Proof.StockDivRhsWitness
import FV.Backend.Proof.StockDivRootMatch
import FV.Backend.Proof.StockDivSafeMatch
import FV.Backend.Proof.StockDivSafeMatchObserved
import FV.Backend.Proof.StockDivSafeObservations
import FV.Backend.Proof.StockDivSafeValues
import FV.Backend.Proof.StockDivSdiv16BoundaryWitness
import FV.Backend.Proof.StockDivSdiv16Witness
import FV.Backend.Proof.StockDivSdiv16WitnessRuns
import FV.Backend.Proof.StockDivSdiv32BoundaryWitness
import FV.Backend.Proof.StockDivSdiv32Witness
import FV.Backend.Proof.StockDivSdiv32WitnessRuns
import FV.Backend.Proof.StockDivSdiv64BoundaryWitness
import FV.Backend.Proof.StockDivSdiv64Witness
import FV.Backend.Proof.StockDivSdiv64WitnessRuns
import FV.Backend.Proof.StockDivSdiv8BoundaryWitness
import FV.Backend.Proof.StockDivSdiv8Witness
import FV.Backend.Proof.StockDivSdiv8WitnessRuns
import FV.Backend.Proof.StockDivSdivSafe16Witness
import FV.Backend.Proof.StockDivSdivSafe16WitnessRuns
import FV.Backend.Proof.StockDivSdivSafe32Witness
import FV.Backend.Proof.StockDivSdivSafe32WitnessRuns
import FV.Backend.Proof.StockDivSdivSafe64Witness
import FV.Backend.Proof.StockDivSdivSafe64WitnessRuns
import FV.Backend.Proof.StockDivSdivSafe8Witness
import FV.Backend.Proof.StockDivSdivSafe8WitnessRuns
import FV.Backend.Proof.StockDivSelected
import FV.Backend.Proof.StockDivSelectedWitness
import FV.Backend.Proof.StockDivSignedObservations
import FV.Backend.Proof.StockDivSignedRecordReceipts
import FV.Backend.Proof.StockDivSignedRecordValues
import FV.Backend.Proof.StockDivSignedSelected
import FV.Backend.Proof.StockDivSignedSelectedWitness
import FV.Backend.Proof.StockDivSignedSourceTrap
import FV.Backend.Proof.StockDivSignedSourceValues
import FV.Backend.Proof.StockDivSignedValues
import FV.Backend.Proof.StockDivSourceOverflow
import FV.Backend.Proof.StockDivSourceRequests
import FV.Backend.Proof.StockDivSourceTrap
import FV.Backend.Proof.StockDivSrem16BoundaryWitness
import FV.Backend.Proof.StockDivSrem16Witness
import FV.Backend.Proof.StockDivSrem16WitnessRuns
import FV.Backend.Proof.StockDivSrem32BoundaryWitness
import FV.Backend.Proof.StockDivSrem32Witness
import FV.Backend.Proof.StockDivSrem32WitnessRuns
import FV.Backend.Proof.StockDivSrem64BoundaryWitness
import FV.Backend.Proof.StockDivSrem64Witness
import FV.Backend.Proof.StockDivSrem64WitnessRuns
import FV.Backend.Proof.StockDivSrem8BoundaryWitness
import FV.Backend.Proof.StockDivSrem8Witness
import FV.Backend.Proof.StockDivSrem8WitnessRuns
import FV.Backend.Proof.StockDivUdiv16Witness
import FV.Backend.Proof.StockDivUdiv16WitnessRuns
import FV.Backend.Proof.StockDivUdiv32Witness
import FV.Backend.Proof.StockDivUdiv32WitnessRuns
import FV.Backend.Proof.StockDivUdiv8Witness
import FV.Backend.Proof.StockDivUdiv8WitnessRuns
import FV.Backend.Proof.StockDivUdivNarrowRecordValues
import FV.Backend.Proof.StockDivUdivNarrowSourceValues
import FV.Backend.Proof.StockDivUdivNarrowValues
import FV.Backend.Proof.StockDivUdivValues
import FV.Backend.Proof.StockDivUdivWideRecordValues
import FV.Backend.Proof.StockDivUdivWideSourceValues
import FV.Backend.Proof.StockDivUdivWideValues
import FV.Backend.Proof.StockDivUdivWideWitness
import FV.Backend.Proof.StockDivUdivWideWitnessRuns
import FV.Backend.Proof.StockDivUrem16Witness
import FV.Backend.Proof.StockDivUrem16WitnessRuns
import FV.Backend.Proof.StockDivUrem32Witness
import FV.Backend.Proof.StockDivUrem32WitnessRuns
import FV.Backend.Proof.StockDivUrem64Witness
import FV.Backend.Proof.StockDivUrem64WitnessRuns
import FV.Backend.Proof.StockDivUrem8Witness
import FV.Backend.Proof.StockDivUrem8WitnessRuns
import FV.Backend.Proof.StockDivValueTransfer
import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockExtendSemantics
import FV.Backend.Proof.StockExtendValues
import FV.Backend.Proof.StockExtendWitness
import FV.Backend.Proof.StockFreshRecordValues
import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.StockHighMulDispatch
import FV.Backend.Proof.StockHighMulMatch
import FV.Backend.Proof.StockHighMulNarrowRecordValues
import FV.Backend.Proof.StockHighMulNarrowRhs
import FV.Backend.Proof.StockHighMulNarrowSelected
import FV.Backend.Proof.StockHighMulNarrowSemantics
import FV.Backend.Proof.StockHighMulPure
import FV.Backend.Proof.StockHighMulRecordIntervals
import FV.Backend.Proof.StockHighMulRecordValues
import FV.Backend.Proof.StockHighMulRequests
import FV.Backend.Proof.StockHighMulRhs
import FV.Backend.Proof.StockHighMulSelected
import FV.Backend.Proof.StockHighMulSemantics
import FV.Backend.Proof.StockHighMulSourceValues
import FV.Backend.Proof.StockHighMulWideRecordValues
import FV.Backend.Proof.StockHighMulWitness
import FV.Backend.Proof.StockHighMulWitnessRuns
import FV.Backend.Proof.StockImm12Helper
import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.StockLogicalLookthrough
import FV.Backend.Proof.StockLogicalNotLookthrough
import FV.Backend.Proof.StockLogicalNotMatch
import FV.Backend.Proof.StockLogicalNotReceipts
import FV.Backend.Proof.StockLogicalNotRecord
import FV.Backend.Proof.StockLogicalNotRecordWitness
import FV.Backend.Proof.StockLogicalNotRootValues
import FV.Backend.Proof.StockLogicalNotSemantics
import FV.Backend.Proof.StockLogicalNotValues
import FV.Backend.Proof.StockLogicalNotWitness
import FV.Backend.Proof.StockLogicalNotXor
import FV.Backend.Proof.StockLogicalNotXorFusedWitness
import FV.Backend.Proof.StockLogicalNotXorRecord
import FV.Backend.Proof.StockLogicalNotXorWitness
import FV.Backend.Proof.StockLogicalObserved
import FV.Backend.Proof.StockLogicalRrr
import FV.Backend.Proof.StockLogicalSelected
import FV.Backend.Proof.StockLogicalSemantics
import FV.Backend.Proof.StockLogicalSourceWitness
import FV.Backend.Proof.StockLogicalValues
import FV.Backend.Proof.StockMulFusedMatch
import FV.Backend.Proof.StockMulFusedRecordValues
import FV.Backend.Proof.StockMulFusedRhs
import FV.Backend.Proof.StockMulFusedSemantics
import FV.Backend.Proof.StockMulFusedValues
import FV.Backend.Proof.StockMulFusedWitness
import FV.Backend.Proof.StockMulHelper
import FV.Backend.Proof.StockMulRecordValues
import FV.Backend.Proof.StockMulRhs
import FV.Backend.Proof.StockMulSemantics
import FV.Backend.Proof.StockMulValues
import FV.Backend.Proof.StockMulWitness
import FV.Backend.Proof.StockNegDispatchWitness
import FV.Backend.Proof.StockNegRecordValues
import FV.Backend.Proof.StockNegRhs
import FV.Backend.Proof.StockNegSelected
import FV.Backend.Proof.StockNegSemantics
import FV.Backend.Proof.StockNegSourceValues
import FV.Backend.Proof.StockNegWitness
import FV.Backend.Proof.StockPayloadAliasOrigins
import FV.Backend.Proof.StockPopcountMath
import FV.Backend.Proof.StockPopcountNonzeroWitness
import FV.Backend.Proof.StockPopcountPure
import FV.Backend.Proof.StockPopcountRecordValues
import FV.Backend.Proof.StockPopcountRhs
import FV.Backend.Proof.StockPopcountSelected
import FV.Backend.Proof.StockPopcountSemantics
import FV.Backend.Proof.StockPopcountSourceValues
import FV.Backend.Proof.StockPopcountZeroWitness
import FV.Backend.Proof.StockRecordIntervals
import FV.Backend.Proof.StockReduceReceipts
import FV.Backend.Proof.StockReduceRecord
import FV.Backend.Proof.StockReduceSelected
import FV.Backend.Proof.StockReduceSourceValues
import FV.Backend.Proof.StockReduceWitness
import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockReservedTerminal
import FV.Backend.Proof.StockRootOpcode
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.StockRotateAuxWitness
import FV.Backend.Proof.StockRotateLeftImmediateWitness
import FV.Backend.Proof.StockRotateLeftRegisterWitness
import FV.Backend.Proof.StockRotateRightImmediateWitness
import FV.Backend.Proof.StockRotateRightRegisterWitness
import FV.Backend.Proof.StockRotateSourceValues
import FV.Backend.Proof.StockScopePartition
import FV.Backend.Proof.StockScopeRoots
import FV.Backend.Proof.StockScopeRootsWitness
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockShiftHelper
import FV.Backend.Proof.StockShiftMatch
import FV.Backend.Proof.StockShiftPrepValues
import FV.Backend.Proof.StockShiftRecordValues
import FV.Backend.Proof.StockShiftRequests
import FV.Backend.Proof.StockShiftRhs
import FV.Backend.Proof.StockShiftRhsObserved
import FV.Backend.Proof.StockShiftRhsWitness
import FV.Backend.Proof.StockShiftRootMatch
import FV.Backend.Proof.StockShiftRootReceipts
import FV.Backend.Proof.StockShiftRootValues
import FV.Backend.Proof.StockShiftSemantics
import FV.Backend.Proof.StockShiftValues
import FV.Backend.Proof.StockShiftWitness
import FV.Backend.Proof.StockSourceAliasRank
import FV.Backend.Proof.StockSourceAliasRecords
import FV.Backend.Proof.StockSourceTerminal
import FV.Backend.Proof.StockUnaryDispatch
import FV.Backend.Proof.StockUnarySourceValues
import FV.E2E.LinkArm
import FV.E2E.RelaxTotal
import FV.E2E.SizeIn
import FV.Link.Exe
import FV.Link.ExeTotal
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_base_match
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_base_resolved
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_data
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_rhs_observed
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_rhs_run
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_selected_root_values
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_shift_match_receipts
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_shift_match_value
#print axioms Backend.Stock.Proof.Bnot.stock_bnot_shift_resolved
#print axioms Backend.Stock.Proof.Bnot.stock_lower_bnot_available_values
#print axioms Backend.Stock.Proof.Bnot.stock_lower_bnot_record_values
#print axioms Backend.Stock.Proof.Bnot.stock_lower_bnot_record_values_witness
#print axioms Backend.Stock.Proof.Bnot.stock_lower_bnot_source_values_witness
#print axioms Backend.Stock.Proof.Coverage.bindResults_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.bindResults_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.blockCore_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.blockCore_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.blockCore_records_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.blockCore_records_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.branchArgs_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.branchArgs_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.branch_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.branch_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.buildCtx_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.buildCtx_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.built_scanBlock_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.built_scanBlock_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.built_scan_slots
#print axioms Backend.Stock.Proof.Coverage.built_scan_slots_witness
#print axioms Backend.Stock.Proof.Coverage.emission_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.emission_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.emission_retTrap_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.emission_retTrap_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.lower_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.lower_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.lower_record_noOpportunistic
#print axioms Backend.Stock.Proof.Coverage.lower_record_noOpportunistic_witness
#print axioms Backend.Stock.Proof.Coverage.lower_records_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.lower_records_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.node_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.node_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.retTrap_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.retTrap_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.scanBlock_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.scanBlock_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.scanBlock_records_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.scanBlock_records_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.scan_noOpportunistic
#print axioms Backend.Stock.Proof.Coverage.scan_noOpportunistic_witness
#print axioms Backend.Stock.Proof.Coverage.scan_retTrap_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.scan_retTrap_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.scan_source_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.scan_source_noOpportunity_witness
#print axioms Backend.Stock.Proof.Coverage.statement_noOpportunity
#print axioms Backend.Stock.Proof.Coverage.statement_noOpportunity_witness
#print axioms Backend.Stock.Proof.Extent.apply_demand_size
#print axioms Backend.Stock.Proof.Extent.ctor_demand_size
#print axioms Backend.Stock.Proof.Extent.demand_extent_witness
#print axioms Backend.Stock.Proof.Extent.lower_mapped_demand_bounds
#print axioms Backend.Stock.Proof.Extent.lower_record_demand_size
#print axioms Backend.Stock.Proof.Extent.named_demand_size
#print axioms Backend.Stock.Proof.Extent.scanBlock_demand_size
#print axioms Backend.Stock.Proof.Extent.scan_demand_size
#print axioms Backend.Stock.Proof.LogicalForms.stock_logical_forms_witness
#print axioms Backend.Stock.Proof.LogicalForms.stock_logical_imm_helper
#print axioms Backend.Stock.Proof.LogicalForms.stock_logical_shift_helper
#print axioms Backend.Stock.Proof.LogicalForms.stock_rhs_3920
#print axioms Backend.Stock.Proof.LogicalForms.stock_rhs_3923
#print axioms Backend.Stock.Proof.LogicalForms.stock_rhs_3928
#print axioms Backend.Stock.Proof.LogicalForms.stock_rhs_3931
#print axioms Backend.Stock.Proof.LogicalNot.MirrorWitness.stock_lower_logical_not_record_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.MirrorWitness.stock_lower_logical_not_source_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.XorFusedWitness.stock_lower_not_xor_fused_record_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.XorFusedWitness.stock_lower_not_xor_fused_source_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.XorWitness.stock_lower_not_xor_record_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.XorWitness.stock_lower_not_xor_source_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.stock_lower_logical_not_available_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_lower_logical_not_record_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_lower_not_xor_available_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_lower_not_xor_record_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_helper_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_helper_values_witness
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_imm_match_receipts
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_imm_resolved
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_imm_rhs_observed
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_pattern_value
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_rhs_helper
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_root_match
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_root_match_receipts
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_root_match_source
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_root_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_rrr_resolved
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_rrr_rhs_observed
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_selected_root_values
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_shift_match_receipts
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_shift_resolved
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_shift_rhs_observed
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_xor_match_receipts
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_xor_match_source
#print axioms Backend.Stock.Proof.LogicalNot.stock_not_xor_selected_root_values
#print axioms Backend.Stock.Proof.LogicalSelected.stock_logical_helper_witness
#print axioms Backend.Stock.Proof.LogicalSelected.stock_logical_rhs_helper
#print axioms Backend.Stock.Proof.LogicalSelected.stock_logical_root_values
#print axioms Backend.Stock.Proof.LogicalSelected.stock_logical_selected_witness
#print axioms Backend.Stock.Proof.LogicalSelected.stock_lower_logical_available_values
#print axioms Backend.Stock.Proof.LogicalSelected.stock_lower_logical_record_inputs_witness
#print axioms Backend.Stock.Proof.LogicalSelected.stock_lower_logical_record_values
#print axioms Backend.Stock.Proof.LogicalSelected.stock_lower_logical_record_values_witness
#print axioms Backend.Stock.Proof.LogicalSelected.stock_lower_logical_selected_receipts
#print axioms Backend.Stock.Proof.LogicalSelected.stock_lower_logical_source_values_witness
#print axioms Backend.Stock.Proof.LogicalSelected.stock_match_logical
#print axioms Backend.Stock.Proof.LogicalSemantics.formBuild
#print axioms Backend.Stock.Proof.LogicalSemantics.formDFG
#print axioms Backend.Stock.Proof.LogicalSemantics.formExtent
#print axioms Backend.Stock.Proof.LogicalSemantics.formHeld
#print axioms Backend.Stock.Proof.LogicalSemantics.formInv
#print axioms Backend.Stock.Proof.LogicalSemantics.formRun
#print axioms Backend.Stock.Proof.LogicalSemantics.formScope
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_constant_match_value
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_constant_match_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_helper_values
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_helper_values_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_imm_match_receipts
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_imm_observed_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_imm_receipts_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_imm_resolved
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_imm_rhs_observed
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_rrr_observed_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_rrr_rhs_observed
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_semantics_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_match_receipts
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_match_value
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_match_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_observed_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_receipts_witness
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_resolved
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_logical_shift_rhs_observed
#print axioms Backend.Stock.Proof.LogicalSemantics.stock_shift_pattern_value
#print axioms Backend.Stock.Proof.LowerSelection.last_rule
#print axioms Backend.Stock.Proof.LowerSelection.rule_mem
#print axioms Backend.Stock.Proof.Neg.DispatchWitness.stock_lower_neg_dispatch_source_witness
#print axioms Backend.Stock.Proof.Neg.Witness.stock_lower_neg_source_values_witness
#print axioms Backend.Stock.Proof.Neg.stock_lower_neg_available_source
#print axioms Backend.Stock.Proof.Neg.stock_lower_neg_available_values
#print axioms Backend.Stock.Proof.Neg.stock_neg_match
#print axioms Backend.Stock.Proof.Neg.stock_neg_resolved
#print axioms Backend.Stock.Proof.Neg.stock_neg_rhs
#print axioms Backend.Stock.Proof.Neg.stock_neg_rhs_requests
#print axioms Backend.Stock.Proof.Neg.stock_neg_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.AuxWitness.stock_addsub_negative_projection_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.ExtensionWitness.stock_lower_addsub_extension_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.ImmediateWitness.stock_lower_addsub_immediate_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.Negative.stock_addsub_negative_match_project
#print axioms Backend.Stock.Proof.ScalarAddSub.Negative.stock_addsub_negative_project
#print axioms Backend.Stock.Proof.ScalarAddSub.Negative.stock_addsub_negative_pure_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.NegativeWitness.stock_lower_addsub_negative_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.ShiftEdgeWitness.stock_lower_addsub_shift_edge_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.ShiftWitness.stock_lower_addsub_shift_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_match_value
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_reg
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_requests
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_resolved
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extended_pattern_value
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_fused_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_resolved
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_imm_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_imm_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_imm_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_match_operand
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_pure_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_put_extended_iff
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_selected_rule_ids
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_match_value
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_requests
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_resolved
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_source_data
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_available_source
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_available_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_available_source
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_available_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_record_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_source_from_step
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_source_operands
#print axioms Backend.Stock.Proof.ScalarBit.BitrevDispatchWitness.stock_lower_bitrev_dispatch_source_witness
#print axioms Backend.Stock.Proof.ScalarBit.BswapDispatchWitness.stock_lower_bswap_dispatch_source_witness
#print axioms Backend.Stock.Proof.ScalarBit.BswapWitness.stock_lower_bswap_source_values_witness
#print axioms Backend.Stock.Proof.ScalarBit.Witness.stock_lower_bitrev_source_values_witness
#print axioms Backend.Stock.Proof.ScalarBit.stock_bit_rr_helper
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_fallback_width
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_narrow_bits
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_narrow_match
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_narrow_rhs
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_narrow_rhs_requests
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_resolved
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_selected_values
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_wide_match
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_wide_rhs
#print axioms Backend.Stock.Proof.ScalarBit.stock_bitrev_wide_rhs_requests
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap16_bits
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap_match
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap_resolved
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap_rhs
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap_rhs_requests
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap_selected_values
#print axioms Backend.Stock.Proof.ScalarBit.stock_bswap_wide_bits
#print axioms Backend.Stock.Proof.ScalarBit.stock_lower_bitrev_available_source
#print axioms Backend.Stock.Proof.ScalarBit.stock_lower_bitrev_available_values
#print axioms Backend.Stock.Proof.ScalarBit.stock_lower_bswap_available_source
#print axioms Backend.Stock.Proof.ScalarBit.stock_lower_bswap_available_values
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.Witness.stock_lower_reduce_source_values_witness
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_lower_reduce_available_source
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_lower_reduce_record_receipts
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_reduce_holds
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_reduce_match
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_reduce_rhs
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_reduce_rhs_requests
#print axioms Backend.Stock.Proof.ScalarCast.Reduce.stock_reduce_selected_receipts
#print axioms Backend.Stock.Proof.ScalarCast.Witness.stock_extend_match_no_type_witness
#print axioms Backend.Stock.Proof.ScalarCast.Witness.stock_lower_extend_source_values_witness
#print axioms Backend.Stock.Proof.ScalarCast.stock_cast_extend_holds
#print axioms Backend.Stock.Proof.ScalarCast.stock_cast_extend_resolved
#print axioms Backend.Stock.Proof.ScalarCast.stock_extend_match
#print axioms Backend.Stock.Proof.ScalarCast.stock_extend_match_no_type
#print axioms Backend.Stock.Proof.ScalarCast.stock_extend_rhs
#print axioms Backend.Stock.Proof.ScalarCast.stock_extend_rhs_requests
#print axioms Backend.Stock.Proof.ScalarCast.stock_extend_selected_values
#print axioms Backend.Stock.Proof.ScalarCast.stock_lower_extend_available_source
#print axioms Backend.Stock.Proof.ScalarCast.stock_lower_extend_available_values
#print axioms Backend.Stock.Proof.ScalarCmp.DefinedDriverWitness.stock_cmp_defined_complete_source_witness
#print axioms Backend.Stock.Proof.ScalarCmp.ParameterDriverWitness.stock_cmp_parameter_complete_source_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_alias_machine_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_carry_flag
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_condition_flags
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_condition_invert
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_condition_observed
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_condition_zero
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_conditions
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_cset_builder
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_defined_driver_observed
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_extension_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_flag_condition_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_flag_condition_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_flags_cset
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_imm_builder
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_nonconstant_emitter_selected
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_nonconstant_emitter_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_nonconstant_selected_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_original_flags
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_original_selection_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_output_observed
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_output_run
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_output_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_parameter_driver_observed
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_parameter_emitter_selected
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_parameter_emitter_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_parameter_root_source_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_parameter_selected_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_predecessor_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_pure_helper
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_pure_helper_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_condition_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_condition_source_values_any_trace
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_condition_source_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_rhs
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_rhs_observed
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_rhs_requests
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_register_rhs_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_root_match
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_root_match_observed
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_root_rhs_calls
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_rr_builder
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_rr_resolved
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_selected_calls
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_selected_calls_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_sets_flags_resolved
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_signed_extension
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_signed_ge_flag
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_signed_predecessor
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_source_data
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_unsigned_extension
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_unsigned_predecessor
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_with_flags_reg
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_zero_condition_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_zero_condition_witness
#print axioms Backend.Stock.Proof.ScalarCmp.stock_cmp_zero_flag
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_nonconstant_available_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_nonconstant_record_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_nonconstant_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_nonconstant_source_operands
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_nonconstant_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_parameter_available_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_parameter_record_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_parameter_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_parameter_source_operands
#print axioms Backend.Stock.Proof.ScalarCmp.stock_lower_cmp_parameter_source_values
#print axioms Backend.Stock.Proof.ScalarCmp.stock_selected_cmp_root
#print axioms Backend.Stock.Proof.ScalarCount.ClzNonzeroWitness.stock_lower_count_source_witness
#print axioms Backend.Stock.Proof.ScalarCount.ClzZeroWitness.stock_lower_count_source_witness
#print axioms Backend.Stock.Proof.ScalarCount.CtzNonzeroWitness.stock_lower_count_source_witness
#print axioms Backend.Stock.Proof.ScalarCount.CtzZeroWitness.stock_lower_count_source_witness
#print axioms Backend.Stock.Proof.ScalarCount.stock_alu_imm12_helper
#print axioms Backend.Stock.Proof.ScalarCount.stock_clz_narrow_rhs
#print axioms Backend.Stock.Proof.ScalarCount.stock_clz_zext_bits
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_clz_narrow_requests
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_clz_narrow_resolved
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_clz_narrow_type
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_ctz_narrow_requests
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_ctz_narrow_resolved
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_match
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_resolved
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_selected_values
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_wide_requests
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_wide_resolved
#print axioms Backend.Stock.Proof.ScalarCount.stock_count_wide_rhs
#print axioms Backend.Stock.Proof.ScalarCount.stock_ctz_narrow_rhs
#print axioms Backend.Stock.Proof.ScalarCount.stock_ctz_sentinel_bits
#print axioms Backend.Stock.Proof.ScalarCount.stock_lower_count_available_source
#print axioms Backend.Stock.Proof.ScalarCount.stock_lower_count_available_values
#print axioms Backend.Stock.Proof.ScalarCount.stock_lower_count_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarCount.stock_selected_count_rule
#print axioms Backend.Stock.Proof.ScalarDiv.BodyValueWitness.stock_div_source_body_witness
#print axioms Backend.Stock.Proof.ScalarDiv.DividendValueWitness.stock_div_dividend_values_witness
#print axioms Backend.Stock.Proof.ScalarDiv.DividendValueWitness.stock_div_plain_dividend_values_witness
#print axioms Backend.Stock.Proof.ScalarDiv.DivisorValueWitness.stock_div_divisor_values_witness
#print axioms Backend.Stock.Proof.ScalarDiv.ImmResolvedWitness.stock_div_imm_resolved_witness
#print axioms Backend.Stock.Proof.ScalarDiv.RemSelectedWitness.stock_div_rem_selected_record_witness
#print axioms Backend.Stock.Proof.ScalarDiv.RequestWitness.stock_div_divisor_request_witness
#print axioms Backend.Stock.Proof.ScalarDiv.RequestWitness.stock_div_divisor_source_values_witness
#print axioms Backend.Stock.Proof.ScalarDiv.RhsWitness.stock_div_actual_rhs_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv16BoundaryWitness.stock_sdiv_16_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv16BoundaryWitness.stock_sdiv_16_overflow_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv16Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv16Witness.stock_sdiv_16_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv16Witness.stock_sdiv_16_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv32BoundaryWitness.stock_sdiv_32_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv32BoundaryWitness.stock_sdiv_32_overflow_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv32Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv32Witness.stock_sdiv_32_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv32Witness.stock_sdiv_32_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv64BoundaryWitness.stock_sdiv_64_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv64BoundaryWitness.stock_sdiv_64_overflow_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv64Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv64Witness.stock_sdiv_64_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv64Witness.stock_sdiv_64_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv8BoundaryWitness.stock_sdiv_8_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv8BoundaryWitness.stock_sdiv_8_overflow_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv8Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv8Witness.stock_sdiv_8_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Sdiv8Witness.stock_sdiv_8_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe16Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe16Witness.stock_sdiv_safe_16_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe32Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe32Witness.stock_sdiv_safe_32_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe64Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe64Witness.stock_sdiv_safe_64_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe8Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.SdivSafe8Witness.stock_sdiv_safe_8_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.SelectedWitness.stock_div_udiv_selected_record_witness
#print axioms Backend.Stock.Proof.ScalarDiv.SignedSelectedWitness.stock_div_sdiv_selected_record_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem16BoundaryWitness.stock_srem_16_minimum_minus_one_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem16BoundaryWitness.stock_srem_16_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem16Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Srem16Witness.stock_srem_16_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem16Witness.stock_srem_16_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem32BoundaryWitness.stock_srem_32_minimum_minus_one_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem32BoundaryWitness.stock_srem_32_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem32Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Srem32Witness.stock_srem_32_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem32Witness.stock_srem_32_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem64BoundaryWitness.stock_srem_64_minimum_minus_one_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem64BoundaryWitness.stock_srem_64_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem64Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Srem64Witness.stock_srem_64_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem64Witness.stock_srem_64_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem8BoundaryWitness.stock_srem_8_minimum_minus_one_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem8BoundaryWitness.stock_srem_8_minimum_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem8Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Srem8Witness.stock_srem_8_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Srem8Witness.stock_srem_8_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv16Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv16Witness.stock_udiv_16_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv16Witness.stock_udiv_16_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv32Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv32Witness.stock_udiv_32_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv32Witness.stock_udiv_32_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv8Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv8Witness.stock_udiv_8_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Udiv8Witness.stock_udiv_8_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.UdivWideWitness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.UdivWideWitness.stock_udiv_wide_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.UdivWideWitness.stock_udiv_wide_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem16Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Urem16Witness.stock_urem_16_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem16Witness.stock_urem_16_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem32Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Urem32Witness.stock_urem_32_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem32Witness.stock_urem_32_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem64Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Urem64Witness.stock_urem_64_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem64Witness.stock_urem_64_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem8Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarDiv.Urem8Witness.stock_urem_8_success_witness
#print axioms Backend.Stock.Proof.ScalarDiv.Urem8Witness.stock_urem_8_zero_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_alias_sem_invariant
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_alias_sem_refines
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_alias_sem_run
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_available_record_outside
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_base_narrow_match
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_base_wide_match
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_condOn_adds1
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_condOn_sub1_vs
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_constant_source_value
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_divisor_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_divisor_observed_with_fuel
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_divisor_reg
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_divisor_source_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_divisor_source_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_divisor_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_driver_alias_idem
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_extended_dividend_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_extension_sub_one
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_general_sdiv_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_held_interval_transfer
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_helper_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_case_lcf32
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_case_lcf64
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_frame_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_legacy_ok
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_operand_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_pure_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_reg
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_imm_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_intmin_code_sem
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_intmin_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_intmin_helper_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_intmin_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_lcf_fold
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_lcf_run
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_lcf_step
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_minimum_source_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_minimum_source_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_movK_ident
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_movK_val
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_msub_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_msub_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_operand_allOnes
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_original_imm_operand_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_alias_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_guard_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_guard_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_guard_run
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_guard_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_overflow_source_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_plain_dividend_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_pure_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_quotient_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_quotient_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_quotient_source_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_narrow_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_narrow_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_narrow_selected_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_record_receipt_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_selected
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_wide_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_wide_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_rem_wide_selected_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_remainder_source_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_resolved_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_safe_narrow_match
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_safe_narrow_match_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_safe_sdiv_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_safe_wide_match
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_safe_wide_match_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_narrow_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_narrow_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_safe_narrow_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_safe_narrow_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_safe_wide_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_safe_wide_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_selected
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_selected_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_wide_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_sdiv_wide_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_shift_intMin
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_signExtend_allOnes
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_source_data
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_source_overflow_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_narrow_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_narrow_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_narrow_selected_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_record_receipt_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_selected
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_wide_from_parts
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_wide_observed
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_udiv_wide_selected_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_zero_alias_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_zero_guard_helper
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_zero_guard_resolved
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_zero_guard_run
#print axioms Backend.Stock.Proof.ScalarDiv.stock_div_zero_guard_witness
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_div_trap_operands
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_narrow_available_source
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_narrow_available_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_narrow_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_narrow_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_narrow_source_operands
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_record_receipt
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_source_trap
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_wide_available_source
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_wide_available_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_wide_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_wide_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_rem_wide_source_operands
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_available_source
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_available_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_record_receipt
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_source_operands
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_sdiv_source_trap
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_narrow_available_source
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_narrow_available_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_narrow_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_narrow_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_narrow_source_operands
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_record_receipt
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_source_trap
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_wide_available_source
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_wide_available_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_wide_record_values
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_wide_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_udiv_wide_source_operands
#print axioms Backend.Stock.Proof.ScalarDiv.stock_selected_div_roots
#print axioms Backend.Stock.Proof.ScalarDiv.stock_selected_div_typed_roots
#print axioms Backend.Stock.Proof.ScalarHighMul.Witness.RunData.observed
#print axioms Backend.Stock.Proof.ScalarHighMul.Witness.stock_lower_highmul_source_values_witness
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_extend_observed
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_extend_reg
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_extend_request
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_from_parts
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_match
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_observed
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_request_observed
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_requests
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_resolved
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_rhs
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_selected
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_narrow_selected_values
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_pure_helper
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_shift_helper
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_source_data
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_helper
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_match
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_observed
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_requests
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_resolved
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_rhs
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_selected
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_highmul_wide_selected_values
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_available_source
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_available_values
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_narrow_available_values
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_narrow_frontier
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_narrow_second_free
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_source_operands
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_lower_highmul_wide_available_values
#print axioms Backend.Stock.Proof.ScalarHighMul.stock_selected_highmul_rule
#print axioms Backend.Stock.Proof.ScalarMul.Fused.Witness.stock_lower_mul_fused_record_values_witness
#print axioms Backend.Stock.Proof.ScalarMul.Fused.Witness.stock_lower_mul_fused_source_values_witness
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_lower_mul_fused_available_values
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_lower_mul_fused_record_values
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_match
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_match_receipts
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_match_source
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_resolved
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_rhs_observed
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_rhs_run
#print axioms Backend.Stock.Proof.ScalarMul.Fused.stock_mul_fused_selected_root_values
#print axioms Backend.Stock.Proof.ScalarMul.Witness.stock_lower_mul_record_values_witness
#print axioms Backend.Stock.Proof.ScalarMul.Witness.stock_lower_mul_source_values_witness
#print axioms Backend.Stock.Proof.ScalarMul.stock_lower_mul_available_values
#print axioms Backend.Stock.Proof.ScalarMul.stock_lower_mul_record_values
#print axioms Backend.Stock.Proof.ScalarMul.stock_madd_helper
#print axioms Backend.Stock.Proof.ScalarMul.stock_msub_helper
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_data
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_match
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_resolved
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_rhs_observed
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_rhs_requests
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_rhs_run
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_rrrr_helper
#print axioms Backend.Stock.Proof.ScalarMul.stock_mul_selected_root_values
#print axioms Backend.Stock.Proof.ScalarPopcount.NonzeroWitness.stock_lower_popcount_source_witness
#print axioms Backend.Stock.Proof.ScalarPopcount.ZeroWitness.stock_lower_popcount_source_witness
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_lower_popcount_available_source
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_lower_popcount_available_values
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_lower_popcount_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcnt16_fin
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcnt32_fin
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcnt64_fin
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcnt8_fin
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_byte
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_count
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_from_vec
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_machine_witness
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_match
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_math_witness
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_pair
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_pure_helper
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_requests
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_resolved
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_rhs
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_rhs_witness
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_selected_values
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_sum
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_sum_full
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_sum_vec
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_popcount_to_vec
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_selected_popcount_rule
#print axioms Backend.Stock.Proof.ScalarRotate.LeftImmediateWitness.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.LeftRegisterWitness.WrappedCount.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.LeftRegisterWitness.ZeroCount.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.LeftRegisterWitness.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.RightImmediateWitness.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.WrappedCount.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.ZeroCount.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.stock_lower_rotate_source_witness
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_immediate_available_source
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_immediate_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_register_available_source
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_register_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_source_operands
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_immediate_available_source
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_immediate_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_register_available_source
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_register_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_helper_variants_witness
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_imm_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_immediate_match
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_immediate_receipts
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_immediate_requests
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_register_requests
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_register_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_rr_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_rr_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_pure_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_pure_sunk
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_register_match
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_rr_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_narrow_immediate_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_narrow_register_state
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_narrow_register_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_wide_immediate_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_wide_register_state
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_wide_register_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_source_data
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_imm_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_imm_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_immediate_requests
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_register_requests
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_zext32
#print axioms Backend.Stock.Proof.ScalarRotate.stock_selected_rotate_rule
#print axioms Backend.Stock.Proof.ScalarRotate.stock_small_rotate_imm_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_small_rotate_neg
#print axioms Backend.Stock.Proof.ScalarRotate.stock_small_rotate_run
#print axioms Backend.Stock.Proof.ScalarShift.Witness.inputs
#print axioms Backend.Stock.Proof.ScalarShift.Witness.scope
#print axioms Backend.Stock.Proof.ScalarShift.Witness.stock_lower_shift_source_values_witness
#print axioms Backend.Stock.Proof.ScalarShift.stock_do_shift_allocates
#print axioms Backend.Stock.Proof.ScalarShift.stock_do_shift_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_do_shift_values_of_count
#print axioms Backend.Stock.Proof.ScalarShift.stock_ext_helper_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_ext_helper_values_witness
#print axioms Backend.Stock.Proof.ScalarShift.stock_ext_passthrough_holds
#print axioms Backend.Stock.Proof.ScalarShift.stock_ext_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_extend_helper
#print axioms Backend.Stock.Proof.ScalarShift.stock_extend_helper_observed
#print axioms Backend.Stock.Proof.ScalarShift.stock_extend_holds
#print axioms Backend.Stock.Proof.ScalarShift.stock_extend_resolved
#print axioms Backend.Stock.Proof.ScalarShift.stock_lower_shift_available_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_sext32_out
#print axioms Backend.Stock.Proof.ScalarShift.stock_sext64_out
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_imm_helper
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_imm_match
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_imm_match_receipts
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_imm_resolved
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_imm_rhs
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_imm_rhs_witness
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_mask_match_receipts
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_mask_resolved
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_mask_rhs
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_mask_rhs_observed
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_mask_rhs_witness
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_prep_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_put_in_regs_iff
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_rhs_receipts
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_root_match
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_root_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_rrr_match_receipts
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_rrr_resolved
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_rrr_rhs
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_rrr_rhs_observed
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_rrr_rhs_witness
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_selected_root_values
#print axioms Backend.Stock.Proof.ScalarShift.stock_shift_semantics_witness
#print axioms Backend.Stock.Proof.ScalarShift.stock_zext32_out
#print axioms Backend.Stock.Proof.ScalarShift.stock_zext64_out
#print axioms Backend.Stock.Proof.ValuesHeld.resolvedResult_available
#print axioms Backend.Stock.Proof.ValuesHeld.resolvedResult_change_needed
#print axioms Backend.Stock.Proof.allocateRequests_returnsPayloadsDisjoint
#print axioms Backend.Stock.Proof.allocateRequests_returnsPayloadsDisjoint_witness
#print axioms Backend.Stock.Proof.available_before_of_after_not_result
#print axioms Backend.Stock.Proof.buildCtx_returnsPayloadsDisjoint
#print axioms Backend.Stock.Proof.buildCtx_returnsPayloadsDisjoint_witness
#print axioms Backend.Stock.Proof.source_single_result_values
#print axioms Backend.Stock.Proof.stock_alu_roots_witness
#print axioms Backend.Stock.Proof.stock_alu_rrr_helper
#print axioms Backend.Stock.Proof.stock_alu_rrr_resolved
#print axioms Backend.Stock.Proof.stock_apply_aliasTargetsAllowed
#print axioms Backend.Stock.Proof.stock_apply_aliasTargetsAllowed_witness
#print axioms Backend.Stock.Proof.stock_apply_demand_mono
#print axioms Backend.Stock.Proof.stock_available_values_witness
#print axioms Backend.Stock.Proof.stock_bindResults_demand
#print axioms Backend.Stock.Proof.stock_bindResults_demand_witness
#print axioms Backend.Stock.Proof.stock_bitrev_opcode_inventory
#print axioms Backend.Stock.Proof.stock_bswap_opcode_inventory
#print axioms Backend.Stock.Proof.stock_ctor_aliasTargetsAllowed
#print axioms Backend.Stock.Proof.stock_ctor_aliasTargetsAllowed_witness
#print axioms Backend.Stock.Proof.stock_ctor_demand_mono
#print axioms Backend.Stock.Proof.stock_demand_mono_witness
#print axioms Backend.Stock.Proof.stock_excluded_root_args
#print axioms Backend.Stock.Proof.stock_excluded_root_match
#print axioms Backend.Stock.Proof.stock_excluded_source_roots_witness
#print axioms Backend.Stock.Proof.stock_iconst_available_resolved
#print axioms Backend.Stock.Proof.stock_iconst_resolved
#print axioms Backend.Stock.Proof.stock_logical_rrr_witness
#print axioms Backend.Stock.Proof.stock_lower_alias_idempotent
#print axioms Backend.Stock.Proof.stock_lower_alias_key_origin
#print axioms Backend.Stock.Proof.stock_lower_alias_key_origin_witness
#print axioms Backend.Stock.Proof.stock_lower_alias_step
#print axioms Backend.Stock.Proof.stock_lower_alias_terminal
#print axioms Backend.Stock.Proof.stock_lower_alias_terminal_witness
#print axioms Backend.Stock.Proof.stock_lower_alias_value
#print axioms Backend.Stock.Proof.stock_lower_alias_wellFounded
#print axioms Backend.Stock.Proof.stock_lower_alu_auto_values_witness
#print axioms Backend.Stock.Proof.stock_lower_alu_available_values
#print axioms Backend.Stock.Proof.stock_lower_alu_available_values_auto_operands
#print axioms Backend.Stock.Proof.stock_lower_alu_available_values_witness
#print axioms Backend.Stock.Proof.stock_lower_alu_operand_coverage
#print axioms Backend.Stock.Proof.stock_lower_alu_record_shape
#print axioms Backend.Stock.Proof.stock_lower_alu_selected_receipts
#print axioms Backend.Stock.Proof.stock_lower_alu_selected_values
#print axioms Backend.Stock.Proof.stock_lower_alu_selected_values_witness
#print axioms Backend.Stock.Proof.stock_lower_available_alias_outside_record
#print axioms Backend.Stock.Proof.stock_lower_available_fresh_frame
#print axioms Backend.Stock.Proof.stock_lower_bitrev_source_by_instruction
#print axioms Backend.Stock.Proof.stock_lower_bitrev_source_from_step
#print axioms Backend.Stock.Proof.stock_lower_blockScanInitialFrontier
#print axioms Backend.Stock.Proof.stock_lower_blockScanInitialFrontier_witness
#print axioms Backend.Stock.Proof.stock_lower_bswap_source_by_instruction
#print axioms Backend.Stock.Proof.stock_lower_bswap_source_from_step
#print axioms Backend.Stock.Proof.stock_lower_constant_available_source
#print axioms Backend.Stock.Proof.stock_lower_constant_available_values
#print axioms Backend.Stock.Proof.stock_lower_constant_available_values_witness
#print axioms Backend.Stock.Proof.stock_lower_final_source_alias_recorded
#print axioms Backend.Stock.Proof.stock_lower_final_source_chain_noCycle
#print axioms Backend.Stock.Proof.stock_lower_final_source_chain_rank
#print axioms Backend.Stock.Proof.stock_lower_final_source_chain_witness
#print axioms Backend.Stock.Proof.stock_lower_fresh_record_values
#print axioms Backend.Stock.Proof.stock_lower_fresh_record_values_auto_demand
#print axioms Backend.Stock.Proof.stock_lower_fresh_record_values_witness
#print axioms Backend.Stock.Proof.stock_lower_neg_source_by_instruction
#print axioms Backend.Stock.Proof.stock_lower_neg_source_from_step
#print axioms Backend.Stock.Proof.stock_lower_payload_aliasOrigin
#print axioms Backend.Stock.Proof.stock_lower_payload_resolves
#print axioms Backend.Stock.Proof.stock_lower_payload_terminal
#print axioms Backend.Stock.Proof.stock_lower_payload_value
#print axioms Backend.Stock.Proof.stock_lower_payload_witness
#print axioms Backend.Stock.Proof.stock_lower_record_args_available
#print axioms Backend.Stock.Proof.stock_lower_record_context
#print axioms Backend.Stock.Proof.stock_lower_record_demand_mono
#print axioms Backend.Stock.Proof.stock_lower_record_fresh_result
#print axioms Backend.Stock.Proof.stock_lower_record_fresh_result_witness
#print axioms Backend.Stock.Proof.stock_lower_record_intervals
#print axioms Backend.Stock.Proof.stock_lower_record_intervals_disjoint
#print axioms Backend.Stock.Proof.stock_lower_record_intervals_witness
#print axioms Backend.Stock.Proof.stock_lower_record_selection
#print axioms Backend.Stock.Proof.stock_lower_record_selection_witness
#print axioms Backend.Stock.Proof.stock_lower_reservedReturn_resolves
#print axioms Backend.Stock.Proof.stock_lower_reservedReturn_resolves_witness
#print axioms Backend.Stock.Proof.stock_lower_reservedReturn_terminal
#print axioms Backend.Stock.Proof.stock_lower_reservedReturn_terminal_witness
#print axioms Backend.Stock.Proof.stock_lower_reservedReturn_value
#print axioms Backend.Stock.Proof.stock_lower_reservedReturn_value_witness
#print axioms Backend.Stock.Proof.stock_lower_source_alias_available
#print axioms Backend.Stock.Proof.stock_lower_source_alias_available_witness
#print axioms Backend.Stock.Proof.stock_lower_source_alias_emitted_record
#print axioms Backend.Stock.Proof.stock_lower_source_alias_provenance
#print axioms Backend.Stock.Proof.stock_lower_source_alias_record
#print axioms Backend.Stock.Proof.stock_lower_source_path_available
#print axioms Backend.Stock.Proof.stock_lower_source_path_fresh_origin
#print axioms Backend.Stock.Proof.stock_lower_source_path_fresh_origin_witness
#print axioms Backend.Stock.Proof.stock_lower_source_record_closure
#print axioms Backend.Stock.Proof.stock_lower_source_record_opcode_ids
#print axioms Backend.Stock.Proof.stock_lower_unary_source_operand
#print axioms Backend.Stock.Proof.stock_lower_undefinedSource_terminal
#print axioms Backend.Stock.Proof.stock_lower_undefinedSource_terminal_witness
#print axioms Backend.Stock.Proof.stock_lower_undefinedSource_value
#print axioms Backend.Stock.Proof.stock_lower_undefinedSource_value_witness
#print axioms Backend.Stock.Proof.stock_match_801
#print axioms Backend.Stock.Proof.stock_match_86
#print axioms Backend.Stock.Proof.stock_named_demand_mono
#print axioms Backend.Stock.Proof.stock_named_lower_selection
#print axioms Backend.Stock.Proof.stock_neg_opcode_inventory
#print axioms Backend.Stock.Proof.stock_put_in_reg_iff
#print axioms Backend.Stock.Proof.stock_recorded_source_alias_provenance
#print axioms Backend.Stock.Proof.stock_recorded_source_alias_rank
#print axioms Backend.Stock.Proof.stock_recorded_source_chain_noCycle
#print axioms Backend.Stock.Proof.stock_recorded_source_chain_rank
#print axioms Backend.Stock.Proof.stock_recorded_source_chain_witness
#print axioms Backend.Stock.Proof.stock_request_success_witness
#print axioms Backend.Stock.Proof.stock_rhs_3916
#print axioms Backend.Stock.Proof.stock_rhs_801
#print axioms Backend.Stock.Proof.stock_rhs_801_observed
#print axioms Backend.Stock.Proof.stock_rhs_801_requests
#print axioms Backend.Stock.Proof.stock_rhs_86
#print axioms Backend.Stock.Proof.stock_rhs_86_observed
#print axioms Backend.Stock.Proof.stock_rhs_86_requests
#print axioms Backend.Stock.Proof.stock_selected_bitrev_rule
#print axioms Backend.Stock.Proof.stock_selected_bswap_rule
#print axioms Backend.Stock.Proof.stock_selected_neg_rule
#print axioms Backend.Stock.Proof.stock_selected_source_closure_witness
#print axioms Backend.Stock.Proof.stock_selected_source_opcode
#print axioms Backend.Stock.Proof.stock_selected_source_opcode_ids
#print axioms Backend.Stock.Proof.stock_selected_source_partition_witness
#print axioms Backend.Stock.Proof.stock_selected_source_root_closure
#print axioms Backend.Stock.Proof.stock_selected_source_root_partition
#print axioms Backend.Stock.Proof.stock_source_opcode_inventory
#print axioms Backend.Stock.Proof.stock_source_provenance_rank
#print axioms Backend.Stock.Proof.stock_source_provenance_rank_witness
#print axioms Backend.Stock.Proof.stock_source_root_partition_counts
#print axioms Backend.Stock.Proof.stock_source_root_partition_witness
#print axioms Backend.Stock.Proof.stock_statement_selectedConstant_context_receipts
#print axioms E2E.LinkCheck.crate_correct_inScope_proven
#print axioms E2E.backend_correct_final_total
#print axioms E2E.backend_correct_final_total_emit_input
#print axioms E2E.backend_correct_final_total_relaxed
#print axioms Link.compileExe_correct
#print axioms Link.compileExe_spec
#print axioms Link.compileExe_total
