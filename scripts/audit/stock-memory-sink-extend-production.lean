import FV.E2E.SemanticNIBoundary
import FV.Backend.ReturnPinProduction
import FV.Backend.Proof.StockMemorySretCopyCompatibility
import FV.Backend.Proof.StockParameterArgsRouteWitness
import FV.Backend.Proof.StockGeneralRouteWitness7
import FV.E2E.ReturnPinProductionWitness

#print axioms E2E.CompiledSemantic.check
#print axioms E2E.CompiledSemantic.alloc
#print axioms E2E.CompiledSemantic.emit
#print axioms E2E.CompiledSemantic.layout
#print axioms E2E.backend_correct_worldX_semantic
#print axioms E2E.CompiledSemanticNI.toSemantic
#print axioms E2E.CompiledSemanticNI.of_checks
#print axioms E2E.backend_correct_world_niX_semantic
#print axioms E2E.CompiledSemanticNI.entryRegs
#print axioms E2E.hasTls_of_vcode_semantic
#print axioms Backend.Stock.MemorySretCopy.previous_file_exact
#print axioms Backend.Stock.MemorySretCopy.previous_routes_exact
#print axioms Backend.Stock.MemorySretCopy.captured_routes_exact
#print axioms Backend.Stock.MemorySretCopy.previous_lower_exact
#print axioms Backend.compileFileReturnPinWhen_retry
#print axioms Backend.compileFileReturnPinWhen_disabled
#print axioms E2E.ReturnPinProductionWitness.mixed_previous_action -- witness: native_decide
#print axioms Backend.Stock.ParameterArgsCfg.NI.RouteFixture.argument_route_witness -- witness: native_decide
#print axioms Backend.Stock.GeneralLoopCfg7.NI.RouteFixture.general_route_witness -- witness: native_decide
