import FV.Backend.Proof.StockForwardDemandWitness
import FV.Backend.Proof.StockCriticalOwners
import FV.Backend.Proof.StockForwardWitness

#print axioms Backend.Stock.Proof.ForwardRpo.successor_after
#print axioms Backend.Stock.Proof.ForwardRpo.diamond_unreachable_witness
#print axioms Backend.Stock.Proof.ForwardSource.source_edge
#print axioms Backend.Stock.Proof.ForwardSource.source_row_size
#print axioms Backend.Stock.Proof.ForwardSource.source_table_ranked
#print axioms Backend.Stock.Proof.ForwardSource.source_successor_after
#print axioms Backend.Stock.Proof.ForwardSource.original_successor_after
#print axioms Backend.Stock.Proof.ForwardSource.successor_labels
#print axioms Backend.Stock.Proof.ForwardSource.successor_demand
#print axioms Backend.Stock.Proof.CriticalOwners.jump_no_edge
#print axioms Backend.Stock.Proof.CriticalOwners.jump_successor
#print axioms Backend.Stock.Proof.ForwardDemandWitness.critical_source_demand_witness

#print axioms Backend.Stock.Proof.ForwardSource.jump_source_row
#print axioms Backend.Stock.Proof.ForwardSource.jump_nonentry_prelude
#print axioms Backend.Stock.Proof.ForwardSource.nonentry_returns
#print axioms Backend.Stock.Proof.ForwardSource.nonentry_traps
#print axioms Backend.Stock.Proof.ForwardSource.scalar_return_frame
#print axioms Backend.Stock.Proof.ForwardSource.scalar_trap_frame
#print axioms Backend.Stock.Proof.ForwardSource.legacy_compatible
#print axioms Backend.Stock.Scalar.domain_of_forward_cfg
#print axioms Backend.Stock.ForwardCfg.domain_of_eligible
#print axioms Backend.Stock.ForwardCfg.sourceOk_sound
#print axioms Backend.Stock.ForwardCfg.check_sound
#print axioms Backend.Stock.Proof.ForwardWitness.checked_driver_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.ForwardWitness.executable_four_block_return_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.ForwardWitness.executable_four_block_trap_witness -- witness: native_decide
