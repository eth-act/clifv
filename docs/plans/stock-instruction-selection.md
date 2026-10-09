# Match stock AArch64 instruction selection in Lean

User-approved plan for #60. Resumed 2026-10-09 on freshly fetched origin/main 33f03f2, branch agent/stock-driver-production.


### Next landing slice: stock constant semantics

The next PR is based directly on main `7a8f263` and contains only the
constructor-scoped interpreter projection and stock constant-materialization
proofs (`IselScopedProjection`, `StockImm`), plus their axiom receipt.
The alias/results prerequisites landed in #100. The slice proves actual stock
`imm` and `iconst` evaluation reuse the existing machine semantics and preserve
scheduling fields. Every public result has an inhabited witness. It changes no
compiler behavior.

Remaining scan, sink, memory and address proof modules stay in the working
stack. Production cutover and whole-driver correctness remain incomplete.
All required local gates passed on the isolated PR branch: full1266, crate959,
corpus114/extrt22/runtests4672zero failures, encoder1292identical/0differing,
E2E1149accepted/0rejected. All14 new theorem/witness audits and seven final
backend/executable axiom checks permit only standard axioms and existing fixed
native certificates. PR101 may merge after green CI.


## Summary

Implement #60 by changing Lean's lowering driver to follow Cranelift 0.136.1 at
pinned commit `46c23a8`: lower consumers before producers, emit definitions only
when selected code needs them, and sink eligible loads using stock's ordering rules.

Include the required lowering, coverage, and end-to-end proof changes. Success
means matching stock's instruction-selection decisions and allocator inputs on
supported cases, eliminating the documented redundant instructions, and retaining
existing verification guarantees.

## Implementation changes

1. **Establish a reproducible baseline and ownership.**
   - Before implementation, update contributor status and agree the lowering/proof
     boundary with @kevaundray in #60.
   - Use a dedicated worktree based on current `main`; preserve the existing local
     diagnostic files.
   - Run the settings-matched stock comparison before changes. Record exact
     matches, accepted functions, and the focused examples from #60.
   - Add optional diagnostic traces for both implementations: block order, initial
     value registers, temporary allocations, selected rules, register demands,
     sinking decisions, and aliases. Stock remains the reference; diagnostics
     must not change its compilation behavior.

2. **Match stock's traversal and register allocation inputs.**
   - Replace layout-order lowering with stock's reverse traversal of its lowered
     block order. Port the relevant reverse-postorder and critical-edge
     construction, including branch-table and exception-edge handling.
   - Lower each block's terminator first, then its body backward. Preserve forward
     order within each rule's emitted instruction sequence when assembling the
     final block.
   - Allocate initial value registers densely in stock's layout traversal order,
     rather than using CLIF value IDs as register IDs. Preallocate exception
     return/payload registers at the corresponding stock allocation points.
   - Carry explicit maps between source values, source blocks, vregs, and lowered
     labels. Resolve aliases consistently in instructions and branch arguments.

3. **Implement demand-driven lowering.**
   - Extend lowering state with selected-code use counts, current
     instruction/block, instruction colors, sunk instructions, and opportunistic
     definitions.
   - Increment demand through all `put_in_reg` variants and through branch
     arguments and implicit ABI uses. Matching an operand as an immediate or
     fused expression must not create an unnecessary register demand.
   - Port stock's separate predicates for memory-order barriers and mandatory
     emission. Preserve calls, stores, atomics, fences, and trapping operations
     even when their results are unused; handle unused nontrapping loads
     according to stock's predicate.
   - Skip an instruction when it has neither mandatory effects nor demanded
     results, or when its effect has already been sunk.
   - Implement opportunistic definitions with stock's same-block and
     unchanged-use-count checks, including its handling of multiple results.

4. **Enable stock-compatible load sinking.**
   - Port stock's `Unused`/`Once`/`Multiple` use analysis, including propagation
     through dependencies and implicit `sret` uses.
   - Make source-definition extraction obey stock's eligibility rules.
     `is_sinkable_inst` must use this analysis and the current instruction color.
   - Implement `sink_inst`: require zero outstanding register demands, check the
     color boundary, mark the producer sunk, and update the scan color.
   - Enable the existing ordinary-load and atomic-load extension rules. Preserve
     access width, flags, ordering, and trap behavior.

## Proofs and interfaces

- Keep the public `lowerFunction : Clif.Function → Except String VCode` interface
  and existing CLI behavior. Diagnostic output is optional.
- Replace the current "one emitted segment per source instruction" replay
  specification with a schedule that records emitted, omitted, sunk, and
  opportunistically supplied definitions.
- Adapt the lowering checker and simulation to prove demanded-value availability,
  valid aliases, omission of unneeded results, and preservation of memory effects
  and traps.
- Reprove `lowerCheck_complete`, `prepDomain_of_lower`, `formsCovered_complete`,
  and the affected end-to-end results for the revised driver. Extend rule-helper
  soundness and coverage analysis for newly reachable sinking rules.
- Retain existing theorem statements and verification strength, without adding
  per-program checker premises or narrowing the accepted input conditions. Add
  non-vacuity witnesses for new top-level theorems.

## Validation and acceptance

- Add focused differential cases for dead constants/comparisons, `bnot` folded
  into `bic`, multiplication folded into `msub`, and redundant stack-address
  materialization.
- Exercise single versus multiple uses, cross-block uses, loops, block arguments,
  sparse value IDs, multiple results, `sret`, and exception edges.
- Test load sinking both when permitted and when blocked by another memory effect
  or control boundary; verify unused trapping loads remain.
- Require identical stock artifacts for isolated instruction-selection fixtures.
  For existing examples with other known differences, require the redundant
  instructions to disappear and record the remaining cause.
- Run the repository's §7 build, proof, filetest, encoder, and end-to-end gates
  under the prescribed memory caps. Require no acceptance regression or new
  failures.
- Run the full settings-matched comparison against the fresh baseline: retain
  existing exact matches, report gained matches, and preserve
  byte/relocation/trap checks without normalization.

## Assumptions and delivery

The scope is instruction selection and the block/register ordering needed to
reproduce it. Direct i128 lowering, callee-save layout, additional settings,
missing operations, and replacing regalloc2 remain separate tasks.

Deliver the driver, checker, proofs, regression cases, and updated contracts
together. Make the revised driver the default once all gates pass, then update
#60 and contributor status with measured results. Full-suite byte equality is not
an acceptance requirement for this issue.

## Resumed implementation status

Merged: #93 diagnostics, #94 experimental stock driver, #95 signed Offset32,
and #96 mapped-context/demand/omission foundations. Production remains legacy.
Original migration is preserved in .worktrees/stock-lowering; port its useful
lemmas to the current-main worktree rather than changing that historical stack.

Current: StockScanSemantics composes actual backward records in forward source
execution order. Its omission adapter uses the stronger #96 theorem, preserves
an arbitrary final alias resolver and memory relation, and connects omissions
to real CLIF small steps. Five public theorems each have non-vacuity witnesses,
including producer/consumer alias redirection and an actual omitted load.
Targeted capped build: 179 jobs passed. Lean MCP diagnostics empty; all ten
theorem/witness axiom audits contain only standard Lean axioms. No default
compiler behavior changes. This is local semantic composition, not a complete
whole-function correctness theorem.

Next required work:
1. Port and validate alias/result and selected-rule transfer, discharging the
   mixed scan local obligations from actual compiler execution.
2. Finish deferred sinking/effects/traps and opportunistic-definition simulation.
3. Compose whole blocks/functions, establish valid final aliases and demanded
   definedness, and prove lowering/checker completeness and output contracts.
4. Adapt existing coverage, E2E and executable compiler/linking proofs without
   new checker assumptions or narrower accepted-input conditions.
5. Switch the default only with full proof/runtime/comparison gates and baseline
   acceptance parity, then publish measured results and update contracts.

Keep slices reviewable; no claim that the preserved large migration is complete.

### Scan-composition slice prepared for review

The bounded scan-composition PR starts from current main33f03f2 and contains
StockScanSemantics plus this plan and its audit receipt. Reverified the exact
PR branch with capped FV/FVTest/backend/E2E/link-check:1262 jobs passed. Lean
MCP diagnostics are clean; five public theorem/five non-vacuity witness audits
use only standard axioms. Runtime/corpus, crate-proofs and final E2E axiom
gates have not been rerun on this isolated branch, so the PR is a draft rather
than merge-ready. The remaining local proof stack is excluded from this slice.

All local merge gates for the isolated scan-composition slice have now passed:
crate-proofs959 jobs; E2E1149 accepted/0rejected/0not-covered; corpus114/0/0,
extrt22/0/0, runnable runtests4672/0/0, and encoder1292 identical/0differ.
The runtime harness separately reports seven not-runnable upstream run lines
and9054 unsupported lines; no runnable result failed or disagreed. Three
E2E/executable axiom audits contain only standard axioms and existing fixed
native certificates. Cached qemu11.1.1/llvm22.1.8 were restored to PATH for the
runtime/encoder checks. Compiler/CLIF semantics are unchanged, so additional
CLIF/optimizer gates do not apply. PR CI still must pass before merging.

### Alias/result transfer reconciled

StockAliasSemantics transports fresh and interval-bounded selected fragments
through the actual final array resolver. Live producer values above the current
fragment's allocation interval remain held. StockResults proves actual virtual
alias installation, fresh resolution, ordered result binding including duplicate
destinations, physical-register copies and rejection of multi-register results.
These are internal transfer facts, not accepted-source restrictions. Scan
composition imports the shared alias definition from this semantic module.

Eleven additional public theorems have eleven non-vacuity witnesses, including
real movz/ALU fragments and the actual result binder. All22 theorem/witness MCP
axiom checks use standard axioms; both modules have no MCP diagnostics. Full
capped FV/FVTest/backend/E2E/link-check build passes1264 jobs. No new native
certificate or heartbeat increase. The selected-rule interpreter bridge and
whole-driver alias bounds still must establish these premises uniformly.

### Alias/result slice prepared on landed scan-composition main

The alias/result PR is based on main850f92a (#99). It contains the original
bounded alias/result transfer modules and the shared alias import in scan
composition; later constant/sinking/load changes are excluded. Exact-branch
verification: full FV/FVTest/backend/E2E/link-check1264 jobs; crate-proofs959;
all22 public theorem/witness MCP audits standard-only and diagnostics clean.
Final backend/executable theorem axiom checks retain the existing fixed native
certificates only. Corpus114/0/0, extrt22/0/0, runnable runtests4672/0/0,
E2E1149/0/0not-covered, encoder1292 identical/0differ. The runtime harness
separately reports7 not-runnable and9054 unsupported lines. Logs use the
/tmp/stock-alias-results-pr-* prefix; audit receipt is
 docs/research/stock-alias-results-audit.json. No runtime/CLIF change.
Final alias interval bounds and complete driver simulation still remain.
