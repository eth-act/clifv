import FV.Backend.Proof.StockLinearCfgWitness
import FV.Backend.Proof.StockLinearCfgTrapWitness
import FV.Backend.Proof.StockLinearCfgCheckWitness

#print axioms Backend.Stock.Proof.Control.direct_successor_guarded_of_demand
#print axioms Backend.Stock.Proof.Control.emit_branch_demand_mono
#print axioms Backend.Stock.Proof.Control.jump_core_input_demand_mono
#print axioms Backend.Stock.Proof.Control.jump_body_input_demand_le_term
#print axioms Backend.Stock.Proof.Control.jump_successor_values_of_demand
#print axioms Backend.Stock.Proof.Control.jump_body_returns_at
#print axioms Backend.Stock.Proof.Control.jump_body_traps_at
#print axioms Backend.Stock.Proof.LinearCfg.block_order_three
#print axioms Backend.Stock.Proof.LinearCfg.actual_traversal
#print axioms Backend.Stock.Proof.LinearCfg.original_node_scan
#print axioms Backend.Stock.Proof.LinearCfg.three_original_scans
#print axioms Backend.Stock.Proof.LinearCfg.three_scan_links
#print axioms Backend.Stock.Proof.LinearCfg.jump_successor_demand
#print axioms Backend.Stock.Proof.LinearCfg.scalar_return_frame
#print axioms Backend.Stock.Proof.LinearCfg.scalar_trap_frame
#print axioms Backend.Stock.Proof.LinearCfg.legacy_compatible
#print axioms Backend.Stock.Scalar.domain_of_linear_cfg
#print axioms Backend.Stock.LinearCfg.domain_of_eligible
#print axioms Backend.Stock.LinearCfg.sourceOk_sound
#print axioms Backend.Stock.LinearCfg.check_sound
#print axioms Backend.Stock.Proof.LinearCfgWitness.actual_linear_driver_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.LinearCfgWitness.actual_demand_transfer_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.LinearCfgWitness.executable_three_block_return_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.LinearCfgWitness.checked_domain_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.LinearCfgTrapWitness.actual_linear_driver_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.LinearCfgTrapWitness.executable_three_block_trap_witness -- witness: native_decide
