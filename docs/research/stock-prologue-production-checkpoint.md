# Actual binary adapter and universal prologue checkpoint

Base #332 /7954ae1f. These additive sources are backed up before consumer migration; they are not a production activation or a completion claim.

`E2E.ActualBinary` ports all24public boundary, depth, stack and checked-image results to the actual compiler table, with the existing machine semantics and boundary conditions. Its proper module build passed; MCP checked `binary_correct_of_checks` with standard axioms and no suspicious source patterns.

The preserved SystemV i64 two-block nop/jump/return proofs now build as proper repository modules. They cover arbitrary names/run metadata, arbitrary source values and memory, complete source execution, real CFG dominance, actual Stock success, code agreement modulo diagnostic fields (proof only), empty successor operand vectors and the actual source/SSA checker. `StockProduction.lower` is a new input-only selector; its proofs establish checked Stock output on eligible inputs, failed-attempt fallback and preservation of all six existing D0 classes. Original selector APIs remain unchanged. No CLI uses the new selector yet.

Targeted gates: proper ActualBinary build377jobs, universal prologue build229jobs, class230jobs and selector233jobs; two audit files46public roots,232owned constants all standard-only. Reused actual linked six-case/twelve-file fixtures are #332 integration evidence; they are not yet a fresh activation test of this new selector.

Next: connect real compiler/checker/linker and generated-proof consumers to this selector, retain original settings/indices/aliases/unwind and verification labels, implement downstream transactional fallback, provide complete machine-boundary witnesses, run current per-PR gates and land the next production class. All original #140 obligations remain open.
