# Actual Stock arithmetic production adapters: active checkpoint

Base main: #345 `fdcff8bb85324e7b0c55b529eaaf2730f83ffe70`.
Branch: `agent/stock-arithmetic-production-adapters`.

The new `Stock.Arithmetic.check` accepts the existing lowering validator or
checks actual Stock provenance, the source arithmetic class, scope/SSA/ABI and
empty edge rows. It does not require Stock/legacy output equality. The additive
`CompiledSemantic` sum constructs actual arithmetic artifacts from executable
checks while retaining `CompiledProduction` and its legacy-validator guarantee.
The linked world/trace consumer covers original source outcomes, ABI returns,
post-call traces and per-state machine guarantees under both cleanup settings.
Original source slots and unused arguments remain supported.

`lowerCheckedSemanticWith` and `compileFileArithmeticWhen` implement candidate
validation and transactional retries with the same source/settings/allocator.
`LinkInput.pipeArithmetic` retains every original static check, replacing only
the lowering verdict with the proved semantic alternative; failed attempts retry
the shipped scalar pipeline. A preservation theorem retains all previously
accepted static verdicts. These new entrypoints are not the default production
activation yet: the old default remains #336.

Targeted validation passes: 850-job normal build through
`FV.E2E.ArithmeticPipelineWitness`, complete raw Stock/Lean allocation/emission/
layout witnesses for both cleanup modes, and a real printed/parsed linker-input
witness whose successful artifact is rejected by the old lowering validator.
All 116 core-owned constants use only standard axioms; 33 witness constants use
two explicitly marked fixed compiler-data native facts. One bundled Lean MCP
check passes; its newly owned server/worker were stopped. Terminal evidence:
`/tmp/stock-arithmetic-adapter-checkpoint/`. Full author gates have not run for
this unfinished implementation packet; this is not merge-ready evidence.

Next: derive raw-Stock non-interference under the original related-world and ABI
register/stack-byte agreement, without a legacy lowering verdict or caller-selected
virtual file. Connect the semantic artifact to whole-program/linker/generated-proof
consumers, then activate the complete class under current per-PR gates. Continue
all original #140 rule/effect, omitted/sunk, simulation and Stock-only completeness
obligations. No original condition, theorem variant, axiom allowance or identity/
stage requirement is relaxed by this checkpoint.
