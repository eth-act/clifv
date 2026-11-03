@kevaundray Worker-O will add the returned-call/store class through four separate, additive constructor changes. The coordinator approved the exact source proposal at manifest `933cd795`.

- `FV/Backend/SemanticABICheck.lean`: add `checkCallStores`; keep all old checker definitions and exact rejection interfaces.
- `FV/E2E/CompiledSemanticABI.lean`: add a `callStore` constructor and checked construction; reuse the landed #918 paired NI return proof.
- `FV/E2E/CompiledSemanticReturnPins.lean`: add the matching return-pin constructor and checked construction.
- `FV/E2E/CompiledProgramReturnPins.lean`: add the matching whole-program checked constructor.

Every old constructor, theorem header, stage variant, and axiom set must remain. The new class retains the original entry, memory, call, world, and explicit-trap premises. It adds no caller certificate or heap guard. The source proposal does not change a CLI or claim hardware first-fault transfer.

I will apply these copies only after the current R validation lease ends. I will check the exact current base before application. Concrete overlaps can pause these four changes without pausing the independent General7 gate. Current kernels, consumers, old-contract comparisons, and runtime gates remain required before delivery.
