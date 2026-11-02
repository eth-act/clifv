import FV.E2E.CompiledProduction
import FV.E2E.ValidatedWitness
import FV.E2E.LoweringProvenance
import FV.Backend.Proof.StockD0ActualConsumerWitness

-- All new public consumer roots; fixed native witnesses are audited separately.
#print axioms E2E.CompiledA.toValidated
#print axioms E2E.backend_correct_validated_ex
#print axioms E2E.backend_correct_of_rules_ex_validated
#print axioms E2E.backend_correct_m4_ex_validated
#print axioms E2E.hasTry_of_hasTryCallA_validated
#print axioms E2E.hasTls_of_vcodeA_validated
#print axioms E2E.outgoing_le_intBaseA_validated
#print axioms E2E.stackArgsAvoid_frameWA_validated
#print axioms E2E.backend_correct_final_ex_validated
#print axioms E2E.Compiled.toValidated
#print axioms E2E.iselSim_relW_validated
#print axioms E2E.backend_correct_world_validated
#print axioms E2E.backend_correct_worldX_validated
#print axioms E2E.instCalls_pair_validated
#print axioms E2E.tryCalls_pair_validated
#print axioms E2E.tryIndCalls_pair_validated
#print axioms E2E.vcode_ni_validated
#print axioms E2E.backend_correct_world_ni_validated
#print axioms E2E.backend_correct_world_niX_validated
#print axioms E2E.CompiledCleanupA.toValidated
#print axioms E2E.CompiledCleanup.toValidated
#print axioms E2E.backend_correct_cleanup_ex_validated
#print axioms E2E.backend_correct_of_rules_cleanup_ex_validated
#print axioms E2E.backend_correct_m4_cleanup_ex_validated
#print axioms E2E.hasTry_of_hasTryCallCleanupA_validated
#print axioms E2E.hasTls_of_vcodeCleanupA_validated
#print axioms E2E.outgoing_le_intBaseCleanupA_validated
#print axioms E2E.stackArgsAvoid_frameWCleanupA_validated
#print axioms E2E.backend_correct_final_cleanup_ex_validated
#print axioms E2E.iselSim_relW_cleanup_validated
#print axioms E2E.backend_correct_world_cleanup_validated
#print axioms E2E.instCalls_pair_value_validated
#print axioms E2E.tryCalls_pair_value_validated
#print axioms E2E.tryIndCalls_pair_value_validated
#print axioms E2E.vcode_ni_value_validated
#print axioms E2E.backend_correct_world_ni_value_validated
#print axioms E2E.backend_correct_worldX_cleanup_validated
#print axioms E2E.backend_correct_world_niX_cleanup_validated
#print axioms E2E.CompiledProduction.lowerOk
#print axioms E2E.CompiledProduction.check
#print axioms E2E.CompiledProduction.alloc
#print axioms E2E.CompiledProduction.emit
#print axioms E2E.CompiledProduction.layout
#print axioms E2E.backend_correct_world_production
#print axioms E2E.backend_correct_world_ni_production
#print axioms E2E.backend_correct_worldX_production
#print axioms E2E.backend_correct_world_niX_production
#print axioms E2E.hasTls_of_vcode_production
#print axioms E2E.stackArgsAvoid_frameW_production
#print axioms E2E.LinkCheck.pipeTWithLowering_spec
#print axioms E2E.LinkCheck.StockConsumerWitness.actual_stock_witness
#print axioms E2E.LinkCheck.StockConsumerWitness.actual_stock_validated_witness
#print axioms E2E.LinkCheck.StockConsumerWitness.actual_stock_cleanup_validated_witness
#print axioms E2E.LinkCheck.StockConsumerWitness.actual_stock_production_modes_witness
#print axioms E2E.ValidatedWitness.try_flags -- witness: native_decide
#print axioms E2E.ValidatedWitness.try_contracts -- witness: native_decide
#print axioms E2E.ValidatedWitness.paired_try_calls -- witness: native_decide
#print axioms E2E.ValidatedWitness.paired_try_indirect_calls -- witness: native_decide
#print axioms E2E.ValidatedWitness.Tls.checks_true -- witness: native_decide
#print axioms E2E.ValidatedWitness.Tls.contracts -- witness: native_decide
#print axioms E2E.ValidatedWitness.paired_try_calls_cleanup -- witness: native_decide
#print axioms E2E.ValidatedWitness.paired_try_indirect_calls_cleanup -- witness: native_decide
