# Stock add/sub/select production activation

Complete single-block i32/i64 add/sub/select functions now use actual Stock
selection through the default compiler, checker, Lean linker and generated proofs.
The classifier covers normal ABI parameters and returns. Source comparison
instructions are not enabled by this class. Prior D0, prologue, scalar and
arithmetic routes and complete-attempt previous/legacy fallback are preserved.

Validated source: `d7f93237450be61d695bb36dfca53a2aae0d91d3`, on arithmetic
squash `95b8710895e24a6bc40014e589b611b792f49b5b`.
[Terminal receipt](stock-mixed-production-activation.json) records all 39gates and
original log hashes/provenance. Historical port receipts are not current passes.

Normal validation covers 2606source modules/2618keys, including 60affected builds,
and 3379library/tooljobs plus crate proofs. All 36checked-in audits pass;
1812owned core constants use only standard axioms;152fixed-witness constants
retain exactly8declared native facts. All1241previous axiom sets and 25 existing
theorem headers are unchanged. One bundled MCP review passes standard-only.

Runtime: 4737 pass/0fail/0disagree retains7known not-runnable cases; encoder: 1321
identical/0different. Both cleanup modes accept 1159 cases and preserve all 1150
original and 1159 prior identities and ordered successful stages. Strict runtime
checks real matched regalloc2 answers across 24 cases and the missing-oracle
negative control. Native execution checks 24 actual Lean-encoded objects with 624
fresh byte executions against 156reference executions:0failures/0disagreements.

Actual linked/generated validation includes 12 roots,18 generated source files,
4 CLI proofs and 962 audited generated constants. Both cleanup modes and current/
retained routes pass. Mixed and sliced 33-function proofs pass. All previous
class runtime/link/generated/CLI retention checks pass, including 24 strict and 24
positive raw arithmetic cases. Verified default Lean-linked fv-demo 21 tests and
survey 53 tests matchLLVM; all 2/2 and 18/18 binaries are verified.

The retained-route test checks the candidate before transactional retry. Its
Plain fixture requires a nonempty retained-name list; direct no-retry probes
check raw/legacy code difference, exact raw byte-match-based membership and the
selected original artifact/ELF/words. Earlier transaction-level comparisons could
retry legacy and did not alone establish raw allocation success; independent
strict positive raw-route checks establish activation.

The original gate controller completed all 39commands and exact axiom parity,
then failed its final metadata report with an undefined reporting variable.
Its failed terminal state is preserved. An independent closing review verified
all required records, hashes, frozen source, identities, headers, axioms, native
results and CLI artifacts. No failed compiler/test command was accepted as a pass.

All remaining original #140 families/effects, omitted/sunk execution, source/block/
whole-driver simulation, Stock-only completeness, optimizer/unwind and final
production-consumer obligations remain open.
