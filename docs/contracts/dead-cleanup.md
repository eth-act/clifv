# Dead selected-instruction cleanup

This stage removes dead pure machine-instruction producers after the existing
instruction selector and its validator, before preparation and allocation.
`lowerFunction`, `lowerCheck` and the original source scope remain unchanged.
The replacement-driver work in PR #135 remains paused.

## Pass and semantic contract

`Backend.DeadCleanup.prune` leaves a CFG-invalid input unchanged. For a valid
CFG, it scans each instruction array backwards and removes an instruction only
when it has a whitelisted pure form, no clobbers, only virtual definitions, at
least one definition, and no live definition. The whitelist (`pureForm`) includes integer
moves/constants/address computations, non-flag-setting arithmetic and logical
operations, multiply-add/subtract, the integer extensions (`uxtb`/`sxth`/…), and `cset` (it
reads the flags but writes only its definition; #552: the boolean of an `icmp` that the
`brif`/`select` rule re-compares, which Cranelift does not lower because no lowered instruction
uses it, `machinst/lower.rs` `lower_clif_block`). Other forms remain in place.
`ABIReadOnly.instruction` keeps its previous producer list (`pureNoFlags`, the whitelist
without the extensions and `cset`).

The scan also removes a compare (`cmp`/`cmn`/`tst` into `xzr`, `cmpForm`, no definition) whose
flags are dead (`flagsDead`): the retained instructions after it reach another compare through
flag-free producers only (`flagFree`: `pureNoFlags` and the extensions). This is the rest of the
`icmp` above, and with it its operand extension (#552 part 2). Its proof relates the two runs
with differing worlds while dropped compares' flags are pending (`Rel.pend`, `FlagsPend`), under
the premise `CmpOverwrite sem`: a compare writes only what the next compare overwrites and
flag-free producers neither read nor change. The value semantics (`valueSem`, `valueSemV`,
`valueSemU`, `valueSemVU`, `valueSemG`, `valueSemGF`) run compares, like pure producers, by
their specification (`specForm`, `mspec`); `*_cmpOverwrite` prove the premise for each, and
`spec_mspec_csem` realizes a compare's specification step by the concrete semantics.
Statements of the generic layers (`prune_correct`, `cleanup_correct`, `memTraps_prune`,
`unwinds_prune`, `tryRaise_prune`, the `*_cleanup_ex*` layer theorems taking `hPure`) gained
this premise (`hcmp`/`hCmp`); the positional lemmas (`rel_kept`, `head_nonpure`,
`nonpure_mem`, `scan_head`, `scan_positions`) gained `cmpForm i = false`: the pass removes more,
so the old statements are false.

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

Consumers composing these theorems without changing them (L1f, #217; e2e.md "The shipped
compiler"): `Link.DeadCleanup.compileExe_correct_peak` (recursive entries, stack for the run's
peak call depth), `compileExe_correct_source` and `compileExe_correct_source_peak` (the original
pre-`i128`-legalisation program), in `FV/E2E/DeadCleanupExecPeak.lean` and
`FV/Link/DeadCleanupExe{Peak,Source}.lean`. `lean-link` names the theorems covering each
executable it writes (`coverage:`); `lean-link --verified` / `cargo fv --lean-link --verified`
make an input outside `SrcScopeB`/`InScopeP` an error instead of the bare-linker fallback.

`link-check --dead-cleanup` selects cleanup artifacts and emits matching checker,
binary, crate and stack proofs. The generated input retains allocator fallback
mode. `lean-link --dead-cleanup` selects the matching executable compiler.
`--no-dead-cleanup` selects the legacy path. Cleanup is the default for these tools and compiler helpers. `cargo fv`
explicitly selects cleanup and reports its matching final/optimizer theorem.
Full proof/crate builds and runtime, encoder and E2E identity gates pass for
the validated source; see the final validation receipt. Lowering diagnostics retain raw
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
plan and completed checkpoints are in `docs/plans/legacy-dead-instruction-cleanup.md`.
