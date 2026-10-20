# Mixed select/add/sub production implementation

Status: implementation prepared on `agent/stock-mixed-production`, based on
`087e91d1`. The module split, shared consumer cases and default adapters are not
yet kernel/runtime validated. They are not a main activation or a completed #140.
The arithmetic delivery checkout remains frozen while its existing author gate
runs; this source-only checkout has no additional build cache or concurrent build.

The verified prototype derives original-source mixed-family records, complete
entry/body/return simulation and no-trap facts. Its flag-threaded semantics retain
actual NZCV changes, realize through the existing value semantics and checked
allocator, and prove full machine non-interference with one internally selected
virtual file. Executable source/provenance checks derive the domain internally.

Prototype evidence is remotely preserved in recovery commit
`20e3dfae6e0772ce82a186d0c6f82699e4492d51`, branch
`agent/stock-driver-wip-backup-20261020T150500Z`. The archive contains
`stock-mixed-classifier-current-packet.json`, the exact checked source and logs.
All 179 owned core constants use only the standard three axioms. The 39 witness
constants allow exactly two fixed compiler-data native facts. All six real
source/provenance/empty-edge checks and twelve ABI/cleanup pipeline configurations
pass. The witness consumes the ninth stack argument, leaves five parameters
unused, declares slot7, and executes dependent add/select/sub plus a dead add.
Source entry and return permit arbitrary argument values and slot addresses.
These prototype checks do not substitute for validation of the split modules.

The implementation extends the existing `CompiledSemantic`/`CompiledSemanticNI`
consumers. Earlier arithmetic/D0/prologue/scalar routes retain their selectors.
New compiler file attempts retry the previous arithmetic pipeline with identical
inputs/settings; the new executable wrapper retries the previous semantic
compiler before legacy. Actual artifact bytes choose retained reconstruction
routes. No source name, virtual-register map or source-execution certificate
restricts the proved class. DCE eligibility and old theorem variants are retained.

Before landing: build all affected modules/tools; audit every owned declaration
and all checked-in public roots with exact previous axiom-set parity; run the
mixed runtime fixture with Lean and matched regalloc2, old-class/history checks,
complete retries, all six ABIs/both cleanup modes; run actual linked and sliced
33-function generated proofs, retained artifacts, all compiler fallback choices,
real default CLIs, original/prior identity-stage parity and verified fv-demo/survey.
Reconcile current main, record terminal receipts, author squash after per-PR gates,
verify the merge tree and notify the integrator. Archive unique evidence and
remove the unneeded clean arithmetic checkout after its landing.

All original #140 uncovered family/effect, omitted/sunk memory/trap/call/CFG,
source/block/whole-driver simulation, Stock-only completeness, optimizer/unwind
and all production-consumer obligations remain open after this class.

Follow-up source review corrected the typed existential binder in
`StockMixedWitness.compiled_semantic_exists`. All24 changed Lean files parse.
An isolated kernel check of the new `accepts_previous` and
`compileWithFallback_spec` against the frozen arithmetic module passes with
exactly the standard three axioms. [Scope and source hashes](stock-mixed-static-routing-check.json).
These checks do not validate the full module port or production adapters;
normal module, witness, runtime and consumer gates above remain pending.
