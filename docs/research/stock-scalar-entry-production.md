# Scalar entry bodies in Stock CFG production

Implementation `b0a84c6bdb1f61fc848e7324598c7d267d90aecc`, with fixture/script
corrections through `b0f103011d30fed0eeadf030bac17db500f85261`, extends the
landed dividing-entry class to the complete existing scalar/division/mask
source family. Entry arithmetic, selects, logical operations, NOT, multiplication,
shifts, casts, bit operations, counts, min/max, comparisons, high multiplication,
bmask and nop compose with a scalar return successor. Arbitrary interleavings
retain first-entry traps, inherited values, original source continuation/fuel,
nonempty successor copies, original ABI entry and source slots.

The same input-only class checker derives the existing Scalar.Domain. Existing
compiler/checker/linker/generated-proof adapters and route6 are reused;
indices0–5, original quiet/dividing selectors, old theorem variants, complete
transactional fallback and optimizer/tail/exception routing remain. No allocator,
shared LowerSim, CLIF semantics or machine-model change is introduced.

The source work retains outside-interval frames that existing numerical/root
execution proofs already established. Some wrappers previously discarded those
frames; stronger variants now expose them and keep the old interface as a
wrapper. For one-result roots, actual root allocation supplies the interval
bound. The carry module reuses existing root/operand/binding/value proofs; it
does not introduce a new accepted-program code or value certificate.

Non-vacuity: an actual kernel-checked function executes an entry add feeding a
division, forwards both results, and adds an inherited entry value in its
successor. Instruction-zero7+3, followed by10/3 and inherited7, returns10;
denominator0 traps before the jump. Kernel compilation passed within8GiB,
7.9GiB anonymous peak, following the bounded6GiB retry. The only new fixed
native fact is labelled original-input dominance, confined to witnesses.
Old source-wrapper witnesses continue through the stronger variants.
Two MCP reviews pass: the general domain uses only the standard three axioms;
the complete trap witness adds only that labelled input-dominance fact.
All31 old public theorem headers are exact.

Native/consumer cohort:96 functions, preserving the separate original16-function
dividing-entry and12-function CFG cohorts. The new cohort includes those16 source
shapes and20 representative scalar shapes at each of four widths, nine ABI
arguments, source slot and nonempty successor copies. Mixed-sign high bits,
zero/overflow, first/later traps and real cast-of-comparison remain observable.
Across six ABI configurations, both allocators and both cleanup modes:

- 70 actual integration checks and18 generated global/per-entry proof roots pass.
- 24 actual encoded objects:23040 Lean byte executions against2880 Cranelift
 reference executions, zero failures/disagreements.
- Both retained cohorts pass their34 actual integration checks each.
- Runtime114 corpus+22extra+5755runnable cases, zero disagreements/failures.
- Encoder1398identical, zero differences.
- BothE2E modes1159accepted, original1150 and parent1159 identities and ordered
 successful stages exactly retained.
- Verified fv-demo21matching tests/two verified executable files.

Final author gates, all bound to `b0f10301`:

- Full normal:4051/4051 keys. The healthy original build rebuilt101 modules;
  a final current-publication full check passed after the fixture-only fixes.
- All91 audit files pass. Strict raw-log comparison reports3518 roots, with
  all3499 previous axiom sets exactly unchanged; six declaration-owner
  partitions pass, including every new private frame proof.
- Verified survey:53 matching tests/18 verified executable files.
- Actual crate-proofs package:93 modules,96 successful recorded commands.
- Fresh same-input/settings byte+relocation comparison against main`b94d6cd4`:
  4543 symbols,900→900 exact,zero gains/losses; no candidate function bytes
  change in this captured corpus. This is not unique-function coverage or a
  goal completion percentage.

A raw-source selector diagnostic explains the limit:128 captured instances pass
both the old quiet-entry selector and the new broader selector; none enters
only the new class.267 instances have only the scalar body family,259 have
unconditional jump/return graphs, and139 have at least three blocks. These are
raw captured-input diagnostics, not post-normalization coverage. General CFG
composition, rather than more operation-specific entry packets, is the next
practical delivery target. The broader carry/body proof is reused there.

Source and progress evidence are backed remotely on
`agent/stock-cfg-body-progress-20261025T025359Z`,
`evidence/cfg-body-progress.tar.gz`; progress snapshot098da531679c07a98a8452a98e323025059c1016
predates the final gates; the subsequent terminal snapshot is linked from the PR. Controllers and raw evidence are saved under
`/tmp/stock-scalar-entry-*`. A terminal snapshot preserves the exact source/binary provenance. Publication
changes after the validated source are documentation only; earlier records
retain their actual source heads.

The old multiplying-entry negative control now belongs to the broader class.
Its exact original input remains as positive raw-Stock selection coverage;
a fresh three-block control checks complete previous-route fallback.96-function
programs also produce per-entry proof artifacts, so all four additional Entries
roots are required. Initial harness failures remain saved; no check was dropped.

This advances #140 without closing it. This class still has two blocks and
forwards entry results through the successor argument vector. Arbitrary CFG,
conditional/table/critical edges and loops, effects/memory/calls/exceptions,
original-domain whole-driver simulation and Stock-only/downstream completeness
remain open. Fallback preserves acceptance; it is not a completeness proof.
