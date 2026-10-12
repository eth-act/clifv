# Register alignment by reusing the candidate Stock schedule

The implemented numbering-only experiment improves literal stock agreement from
**671 to 959 exact artifacts (+288, zero lost matches, zero newly rejected
previously compared functions)**. It fixes 28 of the 33 register-only sampled
occurrences. Production still uses the original lowering driver and landed cleanup;
this is an opt-in allocator-ordering wrapper, not the new driver production cutover.

## What was reused and changed

The existing `lean-backend-lowering-trace --stock-schedule` supplies candidate
register order from the paused Stock allocator/lowering implementation. Its
`StockAlloc` layout requests, exception reservations, and Stock context/flow
construction work are reused by executing that existing tracer. No second Stock
allocator or replacement source-semantics proof is introduced. `StockInitialBounds`
contains color-domain bounds, not the allocation injectivity facts themselves;
the latter live in `StockContext` and associated allocation modules.

The candidate schedule is a model implemented in Lean; it is **not a dump of
actual pinned Cranelift allocator inputs**. Actual pinned stock binaries and
metadata remain the comparison reference. The experiment demonstrates an effective
numbering policy, not unique attribution of all discrepancies to one stock heuristic.

The wrapper requires identical allocator-observable structure: block graph,
instruction/operand counts, kinds/positions/constraints, clobbers and consistent
alias relationships. It derives an injective, class-preserving renaming from that
structure and remaps every operand, block parameter and edge argument. Unused IDs
are assigned distinct positions beyond the candidate register domain.
Allocator JSON does not encode instruction opcodes; structural matching is not a
claim that candidate opcodes are identical. Candidate instructions are never used.
The original instructions, selection, order, constraints and preferences remain.
Only virtual numbering in the untrusted allocator request changes. Returned physical
allocations/edits still pass the original Lean allocation checker.

Unsupported/mismatched candidate traces retain the original allocator request.
Unavailable, failing or malformed tracer output falls back to the original backend.
Compiler CLI options are passed through. No theorem statement, acceptance premise,
compiler default, optimizer rule proof or `movK_ident` implementation changes.

## Experiments and results

| Numbering experiment | Focused matches /33 | Paired full comparison |
| --- | ---: | --- |
| Dense initial numbering only | 0 | Not promoted after focused result |
| Blind temporary-order reversal | 24 | 249 gained, 236 lost; rejected |
| Consistent schedule-derived renaming | 28 | 288 gained, zero lost/rejected |
| Actual opt-in wrapper | 28 via the same mapping | 671 -> 959, +288/-0; zero new rejections |

The complete archived comparison inventory has 1,302 files. Paired checks rerun
683 previously supported compilation groups containing all 1,610 function
occurrences that produced comparable artifacts (671 exact and 939 differing).
Unsupported configurations/functions are not counted as newly supported by this
experiment. All 1,610 baseline comparison rows reproduce the main-bc3a34c archive
exactly. All 1,366 fresh baseline/candidate settings receipts were verified against
the unchanged inputs; all 161 relevant stock variants passed repeat verification.
Code, relocations, alignment, traps and dump/ELF consistency are compared literally.
Full execution metadata equivalence is not asserted.

The five focused cases not matched by the schedule mapping are 44, 55, 57, 67 and
73. Their candidate allocator structures differ beyond numbering, so the wrapper
refuses to apply that mapping. This establishes the experiment's boundary, not
that register alignment for those cases is impossible. The [remaining-case
receipt](register-alignment/remaining-focused.json) records the first observed
operand-kind difference; differing instruction counts can shift correspondence.

## Validation

- Normal full FV/FVTest/tools build: 1,422 jobs passed; crate proofs: 1,171 passed.
- Normal E2E checks preserve all 1,150 accepted identities, including legalized
  functions, with zero rejections. This is a source/checker parity gate; it does
  not by itself validate the external numbering wrapper.
- The actual wrapper passes 114 corpus and 22 external-runtime runs and 4,672
  runtests: zero runtime failures/errors/disagreements; seven known non-runnable
  cases remain. The runtime gate exercises original checking with numbering hints.
- With the wrapper, all 1,292 encoder comparisons are identical; zero differing;
  1,332 relocations checked across 453 files.
- Eight targeted tests cover class preservation, sparse/unused IDs, aliases,
  operand reuse/constraints, branch parameters/arguments, malformed/noninjective
  mappings and refusal of differing graphs/constraints.
- Lean MCP reports the existing `Link.DeadCleanup.compileExe_correct` still has
  830 axioms and no source warnings. Compiler/proof sources are byte-unchanged;
  no new trusted assumptions or proof migrations are required for this wrapper.

The host lacked QEMU user emulation and llvm-mc. Validation used temporary
extracted QEMU 11.1.2 and LLVM 22.1.8 tools; system packages were not changed.
An early actual-wrapper comparison incorrectly nested experimental oracles;
that harness configuration was corrected and the complete paired check rerun.
The initial encoder gate also lacked explicit failure reporting for assembly
production; it now reports that failure instead of silently ending at xargs.

## Use and reproduce

Build `lean-backend`, `lean-backend-lowering-trace`, and `lean-regalloc` using the
repository memory caps, then use the opt-in frontend:

```sh
scripts/lean-backend-stock-numbering.py INPUT.clif OUTPUT.o [ordinary backend options]
```

`CLIFV_ALIGNMENT_BACKEND`, `CLIFV_ALIGNMENT_TRACER` and
`CLIFV_ALIGNMENT_ORACLE` optionally select executables; otherwise the repository
builds are used. `LEAN_BACKEND` selects the wrapper in filetest/encoder scripts.
For the stock comparison, use the existing `--lean-compiler` option to select it.
The lowerer and normal CLI defaults remain unchanged.

The focused and complete archived-artifact probes are
`scripts/register-alignment-probe.py` and `scripts/register-alignment-suite.py`.
Their CLI help documents required evidence, archive and executable paths. The
[plan](../plans/minimal-register-alignment.md), [focused results](register-alignment/focused.json),
[schedule comparison](register-alignment/schedule-suite.json),
[actual-wrapper comparison](register-alignment/wrapper-suite.json),
[comparison verification](register-alignment/comparison-verification.json) and
[validation receipt](register-alignment/validation.json) preserve results.
Raw requests, traces and outputs remain under `target/register-alignment/`.

## Relationship to the active driver goal

These results show the saved candidate driver allocation order has substantial
value and can be tested independently. They do **not** complete the new driver's
source simulation/completeness, prove its sinking/reservation semantics, or switch
production to `Stock.lower`. That larger active goal remains unfinished, including
the preserved alias-proof slice in draft #135 and downstream production consumers.
The opt-in wrapper must not be substituted for that goal's completion.
