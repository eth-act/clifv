# Actual Stock fault-aware executable boundary

The current machine checkpoint proves the original fixed function.
It preserves arbitrary source arguments, memory and fuel.
The fixed function reaches a real TrapAtF through the checked allocator.
It does not yet prove that every earlier physical access succeeds.

Four source-only W adapters preserve actGoodXW and the original legalization identity.
They need coherent DeadCleanupRealizesW and DeadCleanupRegLevelW providers.
The broad normal queue owns both providers.

The old executable proof cannot consume the actual Stock artifacts directly.
FV/E2E/DeadCleanupExecMemFault.lean fixes DeadCleanupBinary.art and its legacy resultsCleanup.
Its MapRelRW and evsOkAt_of_goodW arguments supply the correct fault-world relation.
FV/E2E/SemanticExecProven.lean consumes actual CompilerInput.results through BinOkWithResults.
Its executable theorems require TrapsExplicit.
That premise excludes the source memory faults covered by this function.
No Semantic or WithResults fault-aware counterpart exists in the inspected snapshot.

The next additive interface must keep the actual results, preparation mode and binary artifact.
It must consume the proved W source refinement internally.
It must retain MapRelRW and MapFaults without an accepted-input heap guard.
It must derive the no-earlier-fault trace from GoodXW and the original map relation.
It must carry explicit and memory trap outcomes separately until their observable conversion.
The depth and peak adapters must retain their original stack bounds and source environments.
The final compiler/checker/linker/generated consumers must instantiate this contract internally.
A caller execution certificate is not an acceptable final interface.

All old Domain, DomainM, atomic, NoMemTrap, source and peak variants remain unchanged.
Universal root810 refinement remains a separate unresolved obligation.
