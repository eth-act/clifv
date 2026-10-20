# Raw Stock arithmetic: paired executable consumers

Active branch `agent/stock-arithmetic-production-adapters`, based on main#345.
The additive semantic pipeline now proves full source-to-machine non-interference
with one internally selected initial virtual file. The executable ABI-read check
admits pure producers, entry ABI copies, declared stack argument loads and returns.
It derives the finite machine read boundary internally; no source-value, per-record
family or caller-selected virtual-file certificate is added. Original ABI register
and stack-byte agreement transfers the exact full outputs and return pins.

The new `CompiledSemanticNI` retains compatible production artifacts and actual raw
Stock arithmetic artifacts. Whole-program simulation, stack/binary execution,
real ELF executable correctness, original-source and peak-depth consumers use this
contract, retaining the existing CompilerInput data, machine models, linker
non-compilation conditions and all old theorem variants. Existing implementations
and proofs are untouched. Runtime file orchestration and the matching semantic
proof emitter are present; default entrypoint activation is the next step.

Validation: normal 1,155-job build; all six ABI configurations with both cleanup
settings finish actual allocation/emission/layout and ELF compilation. The fixture
has two operations, an actually used ninth stack argument, six unused parameters
and an explicit source slot. Every actual artifact is rejected by the old lowering
validator, so these witnesses do not silently take legacy fallback. Source entry
and execution are proved for arbitrary argument values and caller slot addresses.
All 1,279 core-owned constants are standard-only; 50 fixed-witness constants use
two explicitly marked fixed compiler-data native facts. One bundled Lean MCP
review passes; its owned server/worker were stopped. Durable terminal evidence:
`/tmp/stock-ni-consumer-checkpoint/` (also included in the remote recovery backup).

This checkpoint is not a default activation or merge-ready gate receipt. Next:
switch the actual compiler/checker/linker/generated-proof entrypoints to the paired
semantic path, retain old settings guards and transactional fallback, validate
mixed programs/generated proofs and all current author gates, then author squash.
All original #140 family/effect, omitted/sunk, simulation, Stock-only completeness,
optimizer/unwind and complete-production obligations remain mandatory and active.
