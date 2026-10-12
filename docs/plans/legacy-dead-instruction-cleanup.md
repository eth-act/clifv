# Legacy dead-instruction cleanup

User-approved implementation plan, 2026-10-10. The replacement-driver effort and
draft PR #135 remain paused. This work starts at fresh main `8959127`.

## Current status

The narrow implementation is published in PR #137 at `735a762`, based on main
`b75d724`. Cleanup and its matching compiler, checker, linker and generated-proof
consumers are enabled by default. The original driver, theorem variants and
source scope are preserved. Fresh full comparison gives 465 -> 671 exact
artifacts (+206), zero lost matches/new rejections and all three focused cases
exact. Runtime, encoder, stack allocation and E2E identity parity pass: both
modes accept the same 1,150 functions, including 161 legalized functions.

The required normal builds pass at that validated source: full FV/FVTest/tools
1,417 jobs and crate proofs 1,171 jobs. The seven paired final theorem audits
have exactly unchanged original/cleanup axiom sets; optimizer-proven parity
(8,937 axioms) also passes Lean MCP verification and its source scan. Runtime:
114/114 corpus, 22/22 external runtime and 4,672 passing runtests with zero
failures/errors/disagreements; the seven native-unsupported cases are unchanged.
Encoder: 1,292 identical, zero differing artifacts. Python: 79 passing tests,
two skips. The original declaration source inventory has no missing occurrences;
it is not a kernel proof count. See `final-validation.json`,
`final-paired-root-axioms.json` and `e2e-identity-parity.json` in the research
receipt directory. PR #136 is merged; implementation and validation are complete
for PR #137. Replacement-driver #135 remains paused.

The progress entries below record earlier checkpoints chronologically.

## Acceptance checkpoint

Prototype a conservative post-lowering cleanup before proof migration. Run the
existing stock comparison with identical inputs, settings and toolchain, first
without cleanup and then with cleanup. Require exact code artifacts for
`%band_not_i64`, `%msub_i32` and `%stack_load_small`, a positive full-suite gain,
no loss of any baseline exact-match identity and no new rejected functions.
Compare relocations, alignment and traps as well as bytes. If this fails, stop
and report measured blockers; do not expand scope automatically.

## Implementation after a successful checkpoint

- Keep legacy instruction selection and `lowerCheck` unchanged. Clean validated
  VCode before allocation; preparation/checking operate on cleaned VCode.
- Scan each block backwards, conservatively preserving virtual registers used
  by other blocks and all outgoing edge arguments. Remove an explicitly pure
  instruction only when every definition is virtual and dead, with no clobbers.
- Whitelist integer moves/constants/address computation and non-flag-setting
  arithmetic/logical/multiply-add/subtract instructions. Preserve memory, flags,
  calls, ABI instructions, traps, control flow and all unknown forms.
- Preserve numbering/classes, parameters, edges, signatures and rule history.
  Only instruction arrays change. No load sinking or register renumbering.
- Prove successful execution and observable-result preservation, and preparation
  and allocation structural requirements. Compose the stage into existing
  production E2E/legalization/crate/binary consumers without narrower source
  assumptions or new per-program certificates. Keep existing theorem variants.
- Use lean-mcp, non-vacuity witnesses and permitted-only axiom audits.

## Validation and landing

Cover dead chains, live/cross-block/loop/edge/ABI uses, real-register definitions
and retained effects. Exercise regalloc2 and stack allocation. Run all required
TO-PROVE section 7 builds, filetests, encoder, E2E and proof audits; preserve
accepted function identities, not just aggregate counts.

PR 1 contains measurement evidence, focused regressions and comparison support,
without a production change. PR 2 contains the proved pass, proof composition,
contracts and default enablement together. Retain `--no-dead-cleanup` for diagnosis
and record cleanup mode in comparison reports. Review and validate exact heads,
check fresh main and squash merge under the existing user authorization.

## Progress

- Fresh main fetched: `8959127bf91f93699b674a3148fab441be874140`.
- Worktree: `/home/lee/clifv/.worktrees/legacy-dead-cleanup`.
- Measurement checkpoint passed: 465 -> 674 exact artifacts, 209 gained, zero
  lost and zero new rejections; all three focused cases exact. Full 1,302-file
  inventory compared. One ASLR-dependent stock stage has only unsupported Lean
  functions and contributes no comparisons. See the research receipt/report.
- Prototype archived as research evidence; production unchanged. Proof integration
  and enablement remain next.

- Measurement/report PR #136 landed as `b75d724` after all required gates.
- The proof implementation strengthens boundary liveness to include own-block
  reads, covering self-loops without a new SSA premise. Repeated full comparison:
  465 -> 671 exact (+206), zero lost matches/new rejections, all focused cases
  exact. This conservatively retains three outputs gained by the original
  prototype. Receipts: `global-live-out-{receipt,delta}.json` in the research
  directory.
- New pass, structural/liveness proofs, CFG/edge preservation, finite-run
  simulation and return/trap preservation check in Lean. `cleanup_correct`
  has standard axioms only; real return, trap and edge-copy witnesses check.
- Proof-only value semantics and an adapter to the existing concrete realizer
  check. Production integration, structural pipeline preservation, final E2E
  variants/caller migration and proof/binary parity validation remain. Cleanup
  is not yet enabled in production.

- Local preparation-domain and raw-lowering → cleanup → preparation E2E
  composition are checked. The production guard leaves a CFG-invalid input
  untouched, so the simulation needs no additional source certificate. A kernel
  witness constructs a valid nonempty CFG/domain and exercises an actual removal.
- Concrete final and linker/world/non-interference adapters are being checked;
  allocation totality, consumers, default enablement, witnesses and final gates
  remain. No completed production cutover is claimed.

- Concrete final compiler theorem `backend_correct_final_cleanup` checks with
  the same source/callee/ABI premises. Its 764 transitive axioms exactly match
  `backend_correct_final`: no additions; source scan clean. GOT and guarded
  world-agreement adapters and the positional/head-retention lemmas also check.
- Allocation/control-layout/edge and emission preservation are local work in
  progress. The linker representation boundary is recorded in #60 at
  https://github.com/eth-act/clifv/issues/60#issuecomment-6099312928.

- The real compiler now accepts `--dead-cleanup` / `--no-dead-cleanup`; the
  default remains off until the consumer cutover and final gates are complete.
  Its full comparison is 465 -> 671 (+206), no losses/new rejections, and all
  three focused cases exact. The regalloc2 oracle was explicitly pinned for
  both runs; the harness now records its actual path and hash.
- Concrete final, world, non-interference, allocation-totality and emission
  adapters check. The linker accepts either preserved legacy artifacts or
  cleanup artifacts, and a cleanup checker has a soundness theorem. The final
  theorem's 764 transitive axioms exactly match the baseline set.
- Preparation commutation checks for pruning, reachability, critical-edge
  splitting and block reordering. The exact spill-size proof's supporting
  instruction-body, edge-copy and entry-store lemmas check in lean-mcp.
- Remaining work: transport the baseline linked-input size and availability
  hypotheses; migrate runtime/checker/generated-proof consumers together;
  finish joint non-vacuity and root audits; enable the default; run all final
  proof/runtime/comparison gates and resolve review. A broader capped build
  is currently rebuilding unchanged instruction-selection dependencies.

- Exact baseline prepared spill-size monotonicity and availability transport now
  check, with standard-only lean-mcp root audits. The definite-assignment
  transport preserves the empty-entry witness and introduces no new source
  hypothesis. GOT knowledge and call-site acceptance also transport. Kernel
  witnesses exercise actual deletion jointly with CFG, availability, size and
  GOT facts. Frame/entry and allocator-check consumers, linked-input completeness
  and the final production consumer cutover remain in progress.

- Frame/entry, baseline allocator-check and linked-input completeness transports
  now compile under unchanged source scope. The spill checker has exact baseline
  113-axiom parity; linked-input completeness has exact 826-axiom parity.
- Cleanup binary, stack-bound and executable-instruction theorem variants compile;
  `binary_correct_exec_proven` has exactly the baseline's 764 transitive axioms,
  with no additions/removals and a clean lean-mcp source scan. The original
  theorem variants and generic byte/frame/read proofs remain available/shared.
- Joint witnesses check both legacy and cleanup checkers on the same nonempty
  source with real deletion and a failed-oracle spill fallback. Generated-proof
  wiring compiles locally; generated output and executable compiler/linker
  consumers are being completed. Defaults and final gates remain pending.

- Cleanup executable compilation and totality variants now compile with the same
  input-scope, placement, relocation-range and outside-code hypotheses. Exact
  baseline axiom parity: `compileExe_correct` 830, `compileExe_total` 823.
  A closed nonempty source succeeds through both executable compilers and links
  fewer words with cleanup; its binary facts follow from the actual linked file.
- The cleanup proof generator preserves allocator fallback mode and emits the
  cleanup checker/binary/stack roots. Its generated one-function proof, including
  binary, closed-base, crate and stack statements, checks. Final broad builds and
  optimizer-proven wrapper validation are still running; default remains off.

- Generated split proof checks 33 functions across two slices, including literal
  source names `codeB`, `okB` and `crate_correct`. The optimizer-proven wrapper
  passes a targeted compile using active cleanup dependencies and 58 byte-identical
  unchanged optimizer cache imports from the warm worktree. No cache artifacts
  were copied; normal whole-repository builds remain the final gates.
- Cleanup is now enabled locally in compiler helpers/CLI, E2E checker, linked
  checker/generator and executable linker. Rust consumers explicitly select that
  mode and report the matching final/optimizer theorem. Final validation and
  review are pending; no merge-ready claim is made.
