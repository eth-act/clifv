import FV.E2E.ABIReadCfg
import FV.E2E.CompiledSemanticNI
import FV.E2E.ABIReadCfgTableWitness

set_option Elab.async false

#print axioms E2E.CfgBoundary.refines
#print axioms E2E.CfgBoundary.driver
#print axioms E2E.CfgBoundary.memory
#print axioms E2E.CfgBoundary.checked_step_frame
#print axioms E2E.CfgBoundary.checked_step_transport
#print axioms E2E.CfgBoundary.Realize.step_realize
#print axioms E2E.CfgBoundary.return_transport
#print axioms E2E.CfgBoundary.return_realize
#print axioms E2E.CfgBoundary.machine_return
#print axioms E2E.CfgBoundary.checked_instruction
#print axioms E2E.CompiledSemanticNI.toSemantic
#print axioms E2E.CompiledSemanticNI.of_checks
#print axioms E2E.backend_correct_world_niX_semantic
#print axioms E2E.ABIReadCfgTableWitness.testBit_admitted
#print axioms E2E.ABIReadCfgTableWitness.island_admitted
#print axioms E2E.ABIReadCfgTableWitness.table_admitted
#print axioms E2E.ABIReadCfgTableWitness.testBit_physical_rejected
