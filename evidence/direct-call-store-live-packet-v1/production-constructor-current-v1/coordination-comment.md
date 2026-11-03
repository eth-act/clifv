Worker-O owns an isolated additive constructor reconciliation on current main9a3f25fb. @kevaundray @codygunton

The exact shared boundary is:

- FV/Backend/SemanticABICheck.lean: append result/live call predicates. Preserve checkCalls and its old contracts.
- FV/E2E/CompiledSemanticABI.lean: add resultCall/liveCall cases and derive their checked return contracts.
- FV/E2E/CompiledSemanticReturnPins.lean: add matching mode-aware result/live constructors.
- FV/E2E/CompiledProgramReturnPins.lean: add checked program instances.

All edits remain in owned candidate copies. All old theorem headers and cases remain. StageF variants stay separate. Main keeps the landed stock-config wrapper, I128 replacement, receipts, mode guards and complete retry. No route index changes. The call-store fault profile and executable first-fault closure remain separate required work. This boundary does not touch General7's coordinator-owned shared files. Please flag a concrete overlap.
