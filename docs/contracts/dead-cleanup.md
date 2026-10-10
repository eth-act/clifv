# Dead selected-instruction cleanup

This stage removes dead pure machine-instruction producers after the existing
instruction selector and its validator, before preparation and allocation.
`lowerFunction`, `lowerCheck` and the original source scope remain unchanged.
The replacement-driver work in PR #135 remains paused.

## Pass and semantic contract

`Backend.DeadCleanup.prune` leaves a CFG-invalid input unchanged. For a valid
CFG, it scans each instruction array backwards and removes an instruction only
when it has a whitelisted pure form, no clobbers, only virtual definitions, at
least one definition, and no live definition. The whitelist includes integer
moves/constants/address computations, non-flag-setting arithmetic and logical
operations, and multiply-add/subtract. Other forms remain in place.

The liveness boundary includes every block's reads and outgoing edge arguments,
including the current block's reads. This deliberately conservative choice covers
self-loops without requiring SSA. Operand errors preserve every classed register.
Register numbers/classes, block labels/parameters/edges, signatures and rule
history are preserved. Instruction order within the retained subsequence is
preserved; loads are not sunk and registers are not renumbered.

`cleanup_correct` proves finite-run preservation, including returns, traps and
edge copies. The concrete realizer adapters compose it with the existing backend
simulation. Preparation commutes with cleanup; the transports preserve baseline
definite assignment, entry emptiness, spill-size bounds, frame/entry checks,
GOT/call knowledge, allocation acceptance, control lowering and emission.

## Consumers and proof scope

The `FV/E2E/DeadCleanup*` variants use `CompiledCleanup` and actual cleanup
artifacts. They retain the baseline source, callee, ABI, memory, world,
non-interference, binary, stack and observable-result assumptions. Original
theorem variants remain available. Shared byte/frame/read, ELF and relocation
lemmas retain their original definitions and proofs.

`Link.DeadCleanup.compileExe` uses the same `InScopeP` check and placement,
relocation-range and outside-code conditions as `Link.compileExe`. Its correctness
and totality variants cover the executable it actually writes. Cleanup linker
completeness transports the original prepared-input hypotheses; it does not
introduce an additional source restriction or a per-program correctness
certificate.

`link-check --dead-cleanup` selects cleanup artifacts and emits matching checker,
binary, crate and stack proofs. The generated input retains allocator fallback
mode. `lean-link --dead-cleanup` selects the matching executable compiler.
`--no-dead-cleanup` selects the legacy path. Cleanup is the default for these tools and compiler helpers. `cargo fv`
explicitly selects cleanup and reports its matching final/optimizer theorem.
Final merge gates must validate this cutover. Lowering diagnostics retain raw
selection/replay and also record the post-cleanup allocation input; their
`allocator_input` follows the same cleanup mode as the compiler.

## Evidence

The actual compiler's opt-in comparison across the 1,302-file stock inventory
improves exact artifacts from 465 to 671, with 206 gains, zero lost exact matches
and zero new rejections. `%band_not_i64`, `%msub_i32` and `%stack_load_small` are
exact. Exactness includes bytes, relocations, alignment and traps. This artifact
comparison is not a runtime or unwind-equivalence test.

Against published baseline `b75d724`, transitive axiom sets are unchanged: final
and executable-instruction roots 764 each; prepared allocator checker 113;
linked-input completeness 826; executable compiler correctness 830; executable
compiler totality 823. New general semantic transports use standard Lean axioms.
Closed compilation/linker witnesses use the baseline fixed-receipt convention
and are excluded from production correctness roots.

Receipts are in `docs/research/legacy-dead-instruction-cleanup/`. The implementation
plan and pending gates are in `docs/plans/legacy-dead-instruction-cleanup.md`.
