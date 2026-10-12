# Match stock AArch64 instruction selection in Lean

## Resumed goal, 2026-10-12

Task #140 resumes completing the actual Stock driver proofs and production cutover.
The original-driver cleanup #137 and opt-in numbering hints #139 are landed;
these do not satisfy the driver cutover goal. PR #135 landed as `25154ad`; its 32 audits match. The next bounded slice
proves actual final aliases to fresh targets resolve to those targets and
transports an already-held value through that resolver. Its real emitted-constant
witness installs alias192→193 and inhabits both lookup and value premises.
All four new theorem/witness roots use only the standard three axioms; full
1418/crate1171, runtime4672/0/0, encoder1292/0 and E2E1150/0 pass.
See `docs/research/stock-fresh-value-audit.json` for source/log hashes.
This does not yet prove emitted instruction execution or whole-driver semantics.
PR #141 landed as `dc91199`. A scope check found that the current `LowerScope`
already excludes overflow instructions. `StockOverflowPatterns` now proves that
all seven overflow-specific generated condition patterns and their actual Stock
rule matches cannot succeed under the existing mapped context invariant, with
a nonempty actual context-build witness. This includes the five AArch64 rules
that create opportunistic flag producers. This is a prerequisite, not yet a
whole-driver proof that opportunistic state stays empty. Preserve the existing
source scope; prove reachability before broadening remembered-register semantics.

PR #142 landed as `94b9a34`. The existing 704-entry coverage table and its
statement, terminator and branch root checks also pass with `opportunistic_def`
forbidden (`StockNoOpportunityTable`); the strengthened checks are proved by
kernel reduction without new native certificates. The abstract bot shortcut
cannot admit that constructor on inhabited abstract inputs. Actual other Stock
constructors preserve the entire remembered-definition table
(`StockNoOpportunityCtor`), including demand and payload alias updates.

PR #143 landed as `a71f89f`. StockCoverageSound now transfers the existing fuel
induction to actual Stock.State; StockCoverageCtor supplies all actual mapped
constructor contracts, and StockCoverageOracle proves the real operand-size
helper retains state. StockCoverageModel instantiates the invariant internally:
actual helper runs described by the unchanged fixed summaries preserve the
remembered table and return the described register classes/output shapes.
The context-build variant derives mapped/clean facts, and nonempty witnesses
exercise actual allocation and Size64 oracle evaluation. Nine new public
proof/witness roots pass standard-only kernel and MCP audits. All local gates
pass: full1425/crates1171, runtime4672/0/0, encoder1292/0, E2E1150/0.

PR #144 landed as `a043f9d`. StockCoverageRoots now composes actual named
source-statement and branch roots with checked summaries/pure exclusions, and
proves result binding after real emission retains the remembered table. Six
standard-only roots/witnesses cover a real allocating constant, installed
alias193→194 and a two-block jump chunk. All local gates pass:
full1426/crates1171, runtime4672/0/0, encoder1292/0, E2E1150/0.

PR #145 landed as `59797d1`. The next bounded slice adds return/trap root
preservation, generic result-binding preservation, actual return/trap emission
and the mandatory terminator scan. A real nonempty one-block return function
inhabits root, emission and scan premises; virtual binding installs alias192→194.
Eight new proof/witness roots use standard axioms only. Full1427/crates1171,
runtime4672/0/0, encoder1292/0 and E2E1150/0 pass. See
`docs/research/stock-term-coverage-audit.json`.

PR #146 landed as `26fdfd7`. StockCoverageScans proves actual context building
initializes an empty remembered table, and actual source-body scans retain it
through omission, sinking, commit attempts and emission. Complete scan lists
compose with source/branch/return/trap slot metadata. A real constant-and-return
function emits both instructions and installs alias193→194; its demanded body
record also witnesses the single-scan theorem. Six new roots pass standard-only
normal kernel and MCP run-code audits. Full1428/crates1171, runtime4672/0/0,
encoder1292/0 and E2E1150/0 pass. See `docs/research/stock-scan-coverage-audit.json`.

PR #147 landed as `f953cff`. StockCoverageBlock derives scan-slot metadata,
mapped context and clean patterns uniformly from actual build/scope/block/range
and data preparation, including try-call branch slots. Actual original block
cores now preserve empty remembered definitions through branch emission, outgoing
argument collection and full scans. A real two-block witness emits jump1 and
scans an unused source constant; another real edge collects register192 and
marks demand0→1. Eight new roots/witnesses pass standard-only kernel/MCP audits;
35 normal audits retain the seven final theorem axiom sets. Full1429/crates1171,
runtime4672/0/0, encoder1292/0 and E2E1150/0 pass. See
`docs/research/stock-block-coverage-audit.json`.

PR #148 landed as `080af26`. StockCoverageDriver composes actual original and
critical-edge nodes, derives their bounds from the constructed order, and uses
the exact reverse-index loop to prove successful `Stock.lower` under existing
`LowerScope` returns an empty remembered-definition table. No caller metadata or
new accepted-input certificate is required. The real emitted-call driver witness
is reused; a real critical-edge witness collects register192, marks demand0→1
and emits jump3. Four new roots use standard axioms only in MCP/kernel audits;
39 normal audits retain the seven final theorem axiom sets. Full1430/crates1171,
runtime4672/0/0, encoder1292/0 and E2E1150/0 pass. See
`docs/research/stock-driver-coverage-audit.json`.

PR #149 landed as `41db8a3`. The stronger record invariant now tracks empty
remembered tables at block-scan inputs and both endpoints of every actual
stored record, through scans, cores, nodes and the whole driver.
StockCoverageRecords derives actual record execution and proves opportunistic
binding cannot be a recorded decision: with no remembered entry, zero demands
would have selected omission first. Existing public interfaces are retained;
shared proofs are factored. Ten new standard-only MCP roots and49 normal audits
pass, retaining seven final theorem axiom sets. Full1431/crates1171,
runtime4672/0/0, encoder1292/0 and E2E1150/0 pass. See
`docs/research/stock-record-coverage-audit.json`.

PR #150 landed as `08608f7`. StockSourceTerminal proves actually mapped source
registers without statement definitions, including block parameters, remain
unaliased through the complete driver and are final resolver terminals. Existing
DFG/SSA construction, allocation separation and alias-frame proofs discharge the
exclusions. A real parameter0 stays at192 while a constant installs193→194;
already-held value7 transports through that final resolver. Four new standard-only
MCP roots and53 normal audits pass; seven final theorem axiom sets are unchanged.
Full1432/crates1171, runtime4672/0/0, encoder1292/0 and E2E1150/0 pass. See
`docs/research/stock-source-terminal-audit.json`.

PR #151 landed as `5926b01`. StockReservedTerminal derives separation between
all return/payload reservations across slots, including overwritten requests,
then proves initial exception-return registers remain final alias terminals
through actual whole lowering. Actual final aliases into returns resolve there
and transport already-held values. A real try-call witness installs194→193
while193 stays terminal; populated/cross-slot allocation and value7 witnesses
inhabit all ten new standard-only MCP roots. All63 normal audits retain the
seven final theorem axiom sets. Full1433/crates1171, runtime4672/0/0,
encoder1292/0 and E2E1150/0 pass. See `docs/research/stock-reserved-terminal-audit.json`.

PR #152 landed as `915ab09`. StockPayloadAliasOrigins derives the only new
constructor alias targets from actual try-call return registers. That invariant
composes through nested evaluation, source-result binding, every scan decision,
branch emission, original/critical-edge nodes and the exact whole-driver traversal.
Actual source/reservation separation prevents source writes from changing payload
entries. Every final payload alias targets an initially reserved return, and every
initially reserved payload resolves to an unaliased endpoint. No extra alias-validity
certificate or narrower accepted source scope is introduced. Real constructor and
interpreter witnesses overwrite payload194→197 with194→193; a complete try-call
witness supplies the final reserved target, endpoint and transport of already-held
value7. Execution producing that value is still unproved.
Nine new MCP roots/witnesses use standard axioms only;72 normal audits preserve
all63 previous sets, including the seven final roots. Full1434/crates1171,
runtime4672/0/0 (seven unchanged not-runnable cases), encoder1292/0 and
E2E1150/0 pass; every E2E identity/stage matches the previous checkpoint.
See `docs/research/stock-payload-alias-origins-audit.json`.

Next close defined-source alias chains and
execution establishing reserved/source values, then noninterference and full
value simulation/completeness. The helper theorem is
actual-state preservation, not emitted-instruction value semantics. Keep the
existing source scope and legacy Cov/T6 interfaces unchanged. Instantiate the
remembered-state invariant and compose actual interpreter/term/block/whole-driver
runs. The checked table and constructor frames are prerequisites; they do not
alone establish the whole-driver invariant or any emitted instruction semantics.

Next: source-available final paths, reserved-value semantics and noninterference;
then discharge actual selected/omitted/sunk rule semantics, whole simulation and
completeness, baseline identity/proof parity and real production/checker/linker
cutover. Preserve original theorem variants and assumptions; no per-program
semantic certificate or narrower source scope may substitute for these proofs.
The historical progress entries below are checkpoints, not current scope limits.


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


### Independent constant-result transfer slice

The actual stock constant root now composes with actual result binding and
alias-resolved machine execution in `stock_iconst_bound` and
`stock_iconst_resolved`. Needed mapped source values survive outside the
constant's fresh allocation interval. These are internal driver simulation
obligations; source IDs need not equal register IDs. Final-alias bounds and
noninterference still require the whole-driver invariant.

Both results have inhabited witnesses and pass four Lean MCP checks, with
standard axioms and the six existing fixed `movK_ident` certificates only.
Exact main-based full1269/crate959, corpus114/extrt22/runtests4672zero failures,
encoder1292identical/0differing, E2E1149/0 and seven final theorem axiom audits
pass. The slice may merge after green CI. Whole-driver and production cutover
remain incomplete.

## Continuous landing discipline and scan-bound slice

PRs #99–#104 have landed. This next independent slice adds StockScanBounds:
actual emission, omission, sunk and opportunistic decisions preserve the initial
alias cap through full instruction and tail-recursive block scans. The inhabited
witness installs alias192→197 below cap194, exercising a fresh target above the
cap. It changes no compiler behavior or acceptance predicate.

Four theorem/witness audits through Lean MCP and an exact-branch CLI check use
standard axioms only. Required gates pass: full1271, crate959, corpus114,
extrt22, runtests4672/0 and zero disagreements, encoder1292/0 differences,
E2E1149/0 rejects, and seven final theorem axiom audits.

Publish independently complete slices promptly, prioritize review fixes and
verified squash merges, and refresh main and contributor status after every
merge. Do not accumulate a second ready slice locally while the first awaits
publication. Keep incomplete drafts explicit and out of merge-ready changes.

Next: fresh-frontier and exception-reservation invariants through scans and the
whole driver, then the remaining SSA/load-fusion obligations and whole-driver
correctness/completeness. Production remains legacy; cutover is incomplete.

## Allocation invariants landing slice

After #105 landed as 4c73876, StockAllocationFlow proves that actual
constructors, complete term evaluation, instruction scans and tail-recursive
block scans never decrease nextVreg and preserve preallocated exception
reservations. Call-output witnesses allocate two fresh registers and retain
nonempty reservations; scan witnesses exercise actual opportunistic aliases.
Four public results have four inhabited witnesses. This changes no compiler
behavior and adds no acceptance restriction.

Eight Lean MCP and exact-branch axiom checks use standard axioms only. All
required gates pass: full1272, crate959, corpus114/extrt22, runtests4672/0 and
zero disagreements, encoder1292 identical/0 differing, E2E1149/0 rejected,
and seven final theorem axiom audits. Whole-driver composition and production
cutover remain pending.

## Whole-driver allocation bounds landing slice

StockDriverBounds composes #105/#106 through actual branch roots, branch
argument collection, outgoing edges, original-block scans, critical-edge nodes,
and complete reverse traversal. Every successful Stock.lower bounds its final
alias array by the initial allocation frontier, never decreases that frontier,
and preserves initial exception reservations. These are unconditional output
facts, not extra compiler acceptance predicates or selected-rule assumptions.

The theorem and actual empty-function success witness pass two Lean MCP and
exact-branch standard-only axiom audits. Nonempty alias installation, call-output
allocation and scan witnesses are in the prerequisite modules. Required gates
pass: full1273, crate959, corpus114/extrt22, runtests4672/0 and zero disagreements,
encoder1292 identical/0 differing, E2E1149/0 rejected, seven final theorem audits.

Next: prove final alias availability at each recorded scan input, then complete
global SSA/window exclusions and source simulation. Whole-driver correctness,
completeness and production cutover remain incomplete.

## Final aliases at every actual scan input

After #107 landed as024031f, the next slice proves the final alias array fits
below every recorded instruction-scan input's fresh frontier. StockScanFrontiers
covers each block record; StockDriverBounds carries this through original
blocks, critical-edge nodes, diagnostic accumulation and complete reverse
traversal. This removes the standalone alias-cap obligation for actual full
runs; no compiler acceptance restriction or behavior changes.

The new block witness records an actual opportunistic scan and nontrivial
alias. The whole-driver witness inhabits its sole successful-run premise with
an empty function; it does not claim a nonempty whole-driver execution witness.
Six new/retained theorem/witness audits through MCP and exact-branch CLI checks
use standard axioms only. Required gates pass: full1274, crate959, corpus114,
extrt22, runtests4672/0 and zero disagreements, encoder1292 identical/0 differing,
E2E1149/0 rejected, and seven final theorem axiom audits.

Next: connect the derived alias availability to actual emitted-scan semantics,
then global SSA/window exclusions, load-fusion/address composition and remaining
selected-rule families. Whole-function simulation, completeness, E2E proof
parity and production cutover remain incomplete.

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


### Independent landing slice: actual sink provenance

The next independent PR contains `StockSinkProvenance`,
`StockPatternBindings` and `StockPatternSink` directly on main7a8f263.
Actual pattern matching and iflet/RHS execution identify the selected producer,
preserve its eligibility and source bindings, and reject effect-only traps.
Normal and atomic loads have inhabited witnesses. The slice does not depend on
the pending constant PR and changes no compiler behavior.

All ten public results and ten witnesses passed twenty Lean MCP axiom checks
using standard axioms only. The full capped build passed1267 jobs.
Required local gates passed: crate959; corpus114/114, extrt22/22; runnable
runtests4672/0/0; encoder1292identical/0differ; E2E1149accepted/0rejected.
Seven final backend/executable theorem audits have only standard axioms and
existing fixed native certificates. PR102 may merge after green CI. Whole-driver and production cutover
remain incomplete.


### Independent alias-bound landing slice

`StockAliasBounds` derives exception-register bounds from actual allocation
requests and successful context construction. Every successful external helper
and complete interpreter term evaluation keeps aliases below a fixed cap
when the reserved payload destinations are below it. Actual result binding
grows the array only at preallocated source-result destinations, even if the
selected source register lies above the cap.

Five public results/five witnesses pass all10 standard-only Lean MCP checks.
Witnesses exercise nonempty exception reservations, actual try-call alias
installation retaining an older alias, and result193→197 while array length195
remains below cap196. Full main-based build1270 and crate959 pass; runtime
corpus114/extrt22/runtests4672zero failures, encoder1292identical/0differing,
E2E1149/0 and seven final theorem axiom audits pass. The slice may merge after
green CI. Whole-scan alias preservation and production cutover remain open.
