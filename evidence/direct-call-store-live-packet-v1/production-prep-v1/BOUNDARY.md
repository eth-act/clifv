# Required production boundary

The call/store class needs a separate memory-aware artifact case.
The existing ResultCall.Domain cannot represent this class.
Its returns field quantifies over an arbitrary MR without MemRelOk.
The store needs the existing MemRelOk guarantee.
The new ReturnStoreDomain keeps both original contracts.
The checked machine theorem derives MemRelOk from the existing RelW setup.

Production integration needs these additive changes:

1. Add a separate SemanticABI admission predicate for the new artifact.
2. Preserve checkCalls and checkResultCalls byte for byte.
3. Add a callStore artifact constructor with the checked actual Stock result and original stage variants.
4. Derive its returned and paired machine guarantees through StockCallStoreNI.
5. Reuse the parameterized binary, executable, compiler, source, checker, and emitter kernels.
6. Prepend the new provider to the complete previous provider.
7. Preserve every previous file retry, explicit route, typed mode, callback, and writer.
8. Execute the original caller/callee and distinct float variant through all three CLIs in both modes.
9. Prove the linked ArmRet result and the actual first store fault.

The three constructor files remain frozen:

- FV/E2E/CompiledSemanticABI.lean
- FV/E2E/CompiledSemanticReturnPins.lean
- FV/E2E/CompiledProgramReturnPins.lean

The shared constructor boundary needs the coordinator's release.
This note does not authorize edits to those files.
The independent class needs no edit to them.

Generic callee traps remain a separate required proof.
The existing valueSemU/xrT route and linked induction provide its interfaces.
XCallsOk retains its original returned-callee guarantee.
No initial-heap guard, execution certificate, or returning-callee admission guard is permitted.
