import FV.E2E.SemanticCompilerWitness

#print axioms E2E.ABIReadOnly.refines
#print axioms E2E.ABIReadOnly.memory
#print axioms E2E.ABIReadOnly.driver
#print axioms E2E.ABIReadOnly.instruction_cases
#print axioms E2E.ABIReadOnly.registerRead_argument
#print axioms E2E.ABIReadOnly.stackRead_argument
#print axioms E2E.ABIReadOnly.checked_instruction
#print axioms E2E.ABIReadOnly.step_world
#print axioms E2E.ABIReadOnly.step_transport
#print axioms E2E.ABIReadOnly.star_transport
#print axioms E2E.ABIReadOnly.return_transport
#print axioms E2E.ABIReadOnly.step_control
#print axioms E2E.ABIReadOnly.step_realize
#print axioms E2E.ABIReadOnly.star_realize
#print axioms E2E.ABIReadOnly.return_realize
#print axioms E2E.ABIReadOnly.machine_return
#print axioms E2E.ABIReadOnly.arguments_transport
#print axioms E2E.backend_correct_world_niX_stock_arithmetic
#print axioms E2E.CompiledSemanticNI.toSemantic
#print axioms E2E.CompiledSemanticNI.of_checks
#print axioms E2E.backend_correct_world_niX_semantic
#print axioms E2E.CompiledSemanticNI.entryRegs
#print axioms E2E.CompiledSemanticNI.noTls
#print axioms E2E.hasTls_of_vcode_semantic
#print axioms E2E.stackArgsAvoid_frameW_semantic
#print axioms E2E.backend_correct_world_semantic
#print axioms E2E.backend_correct_world_ni_semantic
#print axioms E2E.backend_correct_program_semantic
#print axioms E2E.LinkCheck.semanticPreparedResults_sound
#print axioms E2E.SemanticStackBound.okB_sound
#print axioms E2E.SemanticBinary.binary_correct
#print axioms Link.SemanticCompilerWith.attempt_correct
#print axioms Link.SemanticCompilerWith.attempt_correct_source
#print axioms Link.SemanticCompilerWith.attempt_correct_source_peak
#print axioms E2E.StockArithmeticNIWitness.source_entry
#print axioms E2E.StockArithmeticNIWitness.source_returns
#print axioms E2E.StockArithmeticNIWitness.checks_true -- witness: native_decide (fixed compiler data)
#print axioms E2E.StockArithmeticNIWitness.compiled_exists -- witness: native_decide (fixed compiler data)
#print axioms E2E.SemanticCompilerWitness.checks_true -- witness: native_decide (fixed compiler data)
#print axioms E2E.SemanticCompilerWitness.compiler_success -- witness: native_decide (fixed compiler data)
