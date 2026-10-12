# Compiler artifact disagreements: investigations and priorities

This is the combined record of both random-sample investigations, all 128 case
analyses, and the current estimate of opportunities to improve byte-for-byte
stock/Lean agreement. Samples come from different revisions and some function
identities overlap; they are not 128 independent examples of current failures.
The original source/byte evidence and reproduction scripts remain in the two
companion directories linked below.

## Current state and opportunity ranking

The narrow dead-instruction cleanup landed in #137 with a paired gain of **206
exact artifacts (465 -> 671), no lost matches and no newly rejected functions**.
It retained the legacy lowering driver and baseline proof scope. The later
current-main comparison at `bc3a34c` has **939 disagreeing function-compilation
occurrences and 671 exact matches**. Unsupported functions/configurations and
expected stock rejections are outside that disagreement population.

Use the post-cleanup 96-case sample to rank the remaining causes. Do not pool its
proportions with the historical 32-case sample: that sample predates the fix and
has a different comparison population.

| Primary cause | Current sample | Rough scale in the 939 disagreements |
| --- | ---: | ---: |
| Register assignment/coalescing | 33/96 | about 320 |
| Repeated comparisons/boolean materialization | 16/96 | about 160 |
| Callee-save/frame layout | 16/96 | about 160 |
| i128 lowering choices | 14/96 | about 140 |
| Retained pure shifts/extensions/constants | 13/96 | about 130 |
| Scheduling, branch layout, atomic extension, unused nontrapping loads | 4/96 combined | about 40 combined |

The last column is `939 * sample_count / 96`, rounded, and estimates the size of
an opportunity category, **not the number a single patch would fix**. Categories
can contain several mechanisms; cases can have secondary differences that remain
after fixing the primary cause. Frequency estimates are uncertain, larger test
families receive more weight, and this is not an exhaustive taxonomy.

Tentative implementation priority, distinct from frequency ranking:

1. **Extend the existing cleanup whitelist.** The roughly 130-case opportunity
   has a comparatively bounded implementation/proof surface: retained shifts,
   extensions and constant sequences. First measure a prototype and retain all
   prior exact matches before investing in proof changes.
2. **Align frame emission separately.** Roughly 160 occurrences may be relevant,
   but paired saves alone will not resolve every difference in save sets, local
   offsets or register choices. This does not require full lowering-driver replacement.
3. **Trace register allocation inputs.** The largest category (roughly 320) is
   still an observation rather than an isolated allocator root cause. Compare
   vreg allocation order, constraints, preferences, lifetimes and coalescing.
4. **Address repeated comparisons.** Roughly 160 occurrences motivate flag-aware
   cleanup or demand-driven lowering. Removing unused CSET and its CMP producer
   involves separate value and flag-liveness obligations.
5. **Split i128 into bounded fixes.** Masking, live copies, carry/comparison
   sequences and paired memory operations are separate opportunities; about 140
   occurrences does not mean one i128 change resolves them all.

This is a hypothesis about gain versus effort. No measured gain-per-effort ranking
exists yet for the proposed changes.

## Relationship to the paused driver work

**Register alignment is a substantial component of the paused WIP, not its whole
scope.** The saved [stock instruction-selection plan](../plans/stock-instruction-selection.md)
explicitly proposes matching stock's lowered block traversal, lowering bodies
backwards, allocating initial value registers densely in stock's layout order,
preallocating exception registers at corresponding points, and resolving aliases
consistently. Those choices affect the instruction stream and the inputs to register
allocation, which can affect final physical-register assignments and coalescing.

The WIP contains a candidate stock initial allocator (`FV/Backend/Lowering/StockAlloc.lean`)
and reverse traversal (`FV/Backend/Lowering/Stock.lean`), plus supporting proofs.
Some supporting slices have landed, but production retains the legacy driver.
The broader plan also includes demand-driven omission, opportunistic definitions,
load sinking, and their source simulation/completeness and end-to-end proof work.
[Draft #135](https://github.com/eth-act/clifv/pull/135) is a bounded alias-proof slice;
it is not a PR containing a completed register-assignment fix.

Our incremental landing removed dead selected pure instructions after the original
lowering check, preserved register numbering/classes, and avoided that whole-driver
cutover. Thus it delivered a large subset of the initial benefit without proving
all of the broader schedule and sinking behavior.

The 33 register-only observations do **not** establish that finishing the whole WIP
is necessary or sufficient to fix them. A narrower allocation-input change may be
possible, and broader driver changes may help several categories at once. We should
measure the candidate against the current cleanup baseline and isolate the relevant
inputs before resuming the remaining proof migrations. The driver effort remains
paused; this document neither resumes it nor claims a new compiler/proof task.

## Current investigation: 96 post-cleanup occurrences

The current sample supplies the ranking above. Case numbers in this section are
**current 01–96**; they are independent of historical case numbers below.

This sample is from main `bc3a34cf018ea024ef8df4b3bda3fde28ebd5874`, **after** the
legacy-driver dead-instruction cleanup in #137. It classifies 96 randomly selected
stock/Lean function-compilation occurrences. All 96 source snapshots and both
instruction streams were inspected; preserved evidence includes literal code,
disassembly, relocations, alignment, traps, original/adapted input, and settings
requests/receipts. Classification describes observed artifact differences and
supported implementation categories; it does not prove execution equivalence.

### Population, draw and provenance

Source: [main comparison run 38093345756](https://github.com/eth-act/clifv/actions/runs/38093345756),
artifact `stock-comparison-artifacts-1`, ID `11684324784`. The pinned stock revision
is `46c23a87dac1465986a8ad53ba6a7ae49372857b`. The complete inventory has 1,302
files and 4,501 function occurrences: 671 exact artifacts, 939 disagreements,
2,413 Lean-unsupported occurrences, 432 unsupported configurations, and 46
expected stock rejections without binaries. The last three groups are outside
this sample, which asks why successfully produced artifacts disagree.

The population is all 939 `different_code_artifact` occurrences. Identity is
`(test path, variant index, function name, comparison row index)`. Numeric stock
function identity (`index` or `id`) and contract `function_indices` disambiguate
repeated names, including `%f` in precise-output compilation tests. Filenames
and function names alone are insufficient identifiers.

A single `secrets.randbits(64)` seed was fixed before inspecting the draw:
`13455975217634421948`. Sample with Python `random.Random(seed).sample` from the
lexicographically sorted population, without replacement, exclusions or redraw.
The draw spans 46 files: 61 `run` captures and 35 `compile` captures. A `run`
capture records stock-prepared functions, not execution of their assertions.
This is an independent new draw from the current population, not a requirement
to exclude survivors of the earlier sample: three function identities overlap
old cases (new 30/old 15, new 56/old 26, new 72/old 5).

The [manifest](artifact-mismatch-sample-96/manifest.json) records the full population,
draw, source/binary hashes and comparison report digest. The
[verification record](artifact-mismatch-sample-96/verification.json) confirms
all 96 receipts, repeatable stock artifacts, source snapshots and literal
comparisons were independently rechecked. Lean dumps match ELF function bytes,
relocations and alignment. The instrumented-source provenance and full Lean
source tree match this checkout. No compiler rebuild or generated-code execution
was required for this archived-artifact investigation.

### Classification

One primary category is assigned per occurrence, with secondary causes retained
in each explanation. These are categories of visible differences, not a claim
that every case has one isolated compiler root cause.

| Primary observed difference | Count | Share of sample | Cases |
| --- | ---: | ---: | --- |
| Register assignment/coalescing only | 33 | 34.4% | 3, 4, 5, 6, 10, 12, 13, 15, 19, 20, 21, 24, 30, 35, 37, 40, 42, 44, 49, 54, 55, 57, 59, 62, 66, 67, 68, 72, 73, 75, 77, 83, 93 |
| Callee saves and stack-frame layout | 16 | 16.7% | 14, 17, 18, 23, 25, 28, 29, 34, 36, 46, 53, 63, 64, 78, 85, 91 |
| Retained pure shifts/extensions/constants | 13 | 13.5% | 2, 22, 26, 32, 61, 70, 74, 80, 82, 87, 88, 95, 96 |
| Repeated comparison/boolean materialization | 16 | 16.7% | 7, 9, 11, 27, 31, 33, 41, 48, 51, 56, 60, 71, 76, 79, 86, 90 |
| i128 legalization and instruction shapes | 14 | 14.6% | 8, 16, 38, 43, 45, 47, 50, 52, 58, 69, 81, 84, 89, 92 |
| Instruction order | 1 | 1.0% | 39 |
| Branch/edge-copy layout | 1 | 1.0% | 1 |
| Atomic-load extension folding | 1 | 1.0% | 65 |
| Unused nontrapping load | 1 | 1.0% | 94 |

All 96 disagree in literal code bytes. Relocations and required alignment match
in every case; trap records differ in 20 cases. Sampled stock code totals 2,624
bytes versus 3,424 Lean bytes (+800, +30.5%). These sizes describe this draw and
are not whole-suite performance estimates. Trap differences remain literal:
frame/extra-instruction cases often move sites, and split i128 memory operations
can also change their structure (case 47). They are not normalized away.

### What the categories mean for next work

**Register assignment/coalescing (33).** Instruction sequences, operand shapes,
widths and immediates agree; register assignments/reuse do not. All 33 additionally
passed a diagnostic comparison replacing only textual GPR tokens. This is not
used to claim byte agreement or semantic equivalence. Some differences are
consistent renaming; others reuse registers differently (e.g. case 19). We have
not traced these to one allocator heuristic. Investigate stock/Lean vreg order,
constraints, preferences, use lifetimes and coalescing before assuming a whole
driver replacement is necessary or sufficient. See `FV/Backend/Isel.lean:1126`
and `FV/Backend/Regalloc.lean:163`.

**Frames (16).** Atomic loop body instruction forms are similar, but Lean saves
registers individually inside a separately allocated frame while stock pairs
saves/restores and uses pre/post-indexed stack adjustment. Frame slots, temporary
registers and branch/trap offsets can contribute too. Exchange cases 17/29/64
also show Lean saving x28 although stock omits that save. The relevant frame
calculation is `FV/Backend/Regalloc.lean:226`; fixed atomic operands are in
`FV/Backend/RegallocOps.lean:232`. This is a separate change from the lowering
driver; paired saves alone do not guarantee every affected artifact matches.

**Retained pure producers (13).** The landed cleanup intentionally has a narrow
whitelist. `extend`, standalone shift operations and `movK` are excluded from
`pureForm`/`pureAlu` (`FV/Backend/DeadCleanup.lean:9–19`). Thus SXTB/SXTW and shifts
remain even when an ADD, load addressing mode, bitfield operation or EXTR has
absorbed their work. Case 87 has an unused MOV/MOVK constant construction; excluded
MOVK reads keep the first constant live. Case 22's final MOV spelling comes from
an extension form. These observations support trying a bounded, proved whitelist
extension before committing to full driver replacement. The cleanup's all-block
read boundary is deliberately conservative; changing it would require separate
reasoning about control flow and register reuse.

**Repeated comparisons (16).** Lean retains comparison/CSET materialization and
repeats comparison for a folded SELECT/extension consumer. Some pair-valued
selects repeat it once per half. Flag-writing/reading forms are not cleaned today.
Removing a CSET result and safely removing its flag producer are distinct
obligations. A flag-aware cleanup or demand-driven lowering could address this
category, but a register-only whitelist expansion cannot remove every extra CMP.
See `FV/Backend/DeadCleanup.lean:14` and `FV/Backend/Isel.lean:1126`.

**i128 lowering (14).** Several results are live rather than dead: identity copies,
explicit shift masks, boolean-based carry/comparison expansion, separate memory
operations instead of pairs, and long wide-shift sequences. `FV/Opt/Legal.lean`
contains the deliberate pure expansions (`copy2`, `shiftNarrow`, wide arithmetic
and comparisons). Cases 45/47 also require paired memory and comparison selection.
These are not all resolved by changing driver traversal. Case 58 is especially
clear: two live identity ORRs versus stock RET only. Case 16 additionally retains
same-destination branches; mixed cases are not charged twice in the primary table.

**Other observations (4).** Case 39 reverses the order of independent half-bit
reversal work; case 1 differs in conditional branch/edge-move scheduling. Their
exact scheduling/allocator root causes remain unresolved. Case 65 still needs
atomic-load/extension folding (`is_sinkable_inst` fails at `Isel.lean:791`). Case
94 retains an unused `notrap` load because cleanup excludes memory operations.
The latter needs the source notrap/effect contract, not speculative deletion of
potentially faulting loads.

### Implications and limits

The old five-category description is not a complete taxonomy: this draw requires
explicit scheduling/CFG and unused-nontrapping-load categories, and separates
retained ordinary producers from repeated flag-producing comparisons. It supports
these as common remaining targets; it does not establish exhaustive causes across
939 disagreements or across unsupported inputs. Test families contain correlated
occurrences, and sampling occurrences weights larger families more heavily than
sampling distinct files would.

The old run had a different comparison population and checkout. Do not infer
that its 983 disagreements fell to 939 solely because of cleanup: the paired
same-compiler experiment is the separate +206/-0 receipt from #137. This new
sample gives no measured improvement prediction for an unimplemented fix.

For further byte agreement, first measure a small extension covering the 13
retained-producer examples and a separate frame-emission experiment; investigate
register inputs using paired traces. Treat repeated comparisons/flag liveness and
live i128 reshaping as separate proof scopes. Full stock driver traversal/sinking
remains a plausible route for several groups, but this sample does not justify
assuming it is the cheapest or necessary fix for all of them. Replacement-driver
#135 remains paused; this report makes no compiler/proof change or task claim.

The comparison contract covers code bytes, relocations, alignment and traps.
Enabled unwind metadata and Lean exception-table export remain incomplete; no
claim of full execution metadata equivalence is made. Static inspection does not
establish that either compiler has wrong-code behavior. Confidence in observable
structure is separated from uncertain allocator/scheduling attribution in the
[machine-readable classification](artifact-mismatch-sample-96/classification.json).

### Every sampled case

Each linked JSON includes both full instruction streams and original/adapted
source; row index distinguishes repeated function names within a variant.

| Case | Test/function occurrence | Primary category | Stock/Lean bytes | Explanation |
| --- | --- | --- | ---: | --- |
| [01](artifact-mismatch-sample-96/cases/01.json) | `runtests/brif.clif` / `%fuzzgen_2`; variant 0, row 10 | Branch/edge-copy layout | 44/44 | Different branch polarity/targets and edge-copy placement for the same block graph; temporary registers also differ. The exact CFG/edge-move scheduling cause remains unresolved. |
| [02](artifact-mismatch-sample-96/cases/02.json) | `isa/aarch64/narrow-arithmetic.clif` / `%add64_32`; variant 0, row 4 | Retained pure shifts/extensions/constants | 8/12 | Unused SXTW precedes ADD with built-in SXTW extension. Standalone extend is outside the cleanup whitelist. |
| [03](artifact-mismatch-sample-96/cases/03.json) | `runtests/or-and-y-with-not-y.clif` / `%or_and_constant_with_not_constant`; variant 0, row 1 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [04](artifact-mismatch-sample-96/cases/04.json) | `runtests/shifts.clif` / `%sshr_all_ones_left_operand`; variant 0, row 77 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [05](artifact-mismatch-sample-96/cases/05.json) | `runtests/fold-bitops.clif` / `%simplify_bor_yxy`; variant 0, row 1 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [06](artifact-mismatch-sample-96/cases/06.json) | `runtests/arithmetic.clif` / `%simplify_icmp_eq_iadd_commute`; variant 0, row 58 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [07](artifact-mismatch-sample-96/cases/07.json) | `runtests/extend-of-compare.clif` / `%uext_icmp_multi_use`; variant 0, row 6 | Repeated comparison/boolean materialization | 24/32 | Lean computes CMP/CSET three times, stock twice; one unused materialized boolean remains. |
| [08](artifact-mismatch-sample-96/cases/08.json) | `runtests/shifts.clif` / `%ishl_i64_i128`; variant 0, row 48 | i128 legalization and instruction shapes | 8/16 | Fresh low-half ORR copy and AND #63 precede LSL; stock uses hardware shift-count masking. |
| [09](artifact-mismatch-sample-96/cases/09.json) | `isa/aarch64/condops.clif` / `%f`; variant 0, row 29 | Repeated comparison/boolean materialization | 20/44 | For a pair-valued select Lean materializes an unused boolean and repeats UXTB/comparison for both halves; stock shares one comparison. |
| [10](artifact-mismatch-sample-96/cases/10.json) | `runtests/arithmetic.clif` / `%test_ule_umin_x`; variant 0, row 68 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [11](artifact-mismatch-sample-96/cases/11.json) | `isa/aarch64/condops.clif` / `%f`; variant 0, row 9 | Repeated comparison/boolean materialization | 20/44 | For a pair-valued select Lean materializes an unused boolean and repeats UXTH/comparison for both halves; stock shares one comparison. |
| [12](artifact-mismatch-sample-96/cases/12.json) | `runtests/arithmetic.clif` / `%fold_isub_bor_bxor_to_band_i32_rt`; variant 0, row 47 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [13](artifact-mismatch-sample-96/cases/13.json) | `runtests/x64-bmi1.clif` / `%blsi64`; variant 0, row 1 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [14](artifact-mismatch-sample-96/cases/14.json) | `isa/aarch64/atomic-rmw.clif` / `%atomic_rmw_nand_i64`; variant 0, row 12 | Callee saves and stack-frame layout | 68/92 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [15](artifact-mismatch-sample-96/cases/15.json) | `runtests/arithmetic-extends.clif` / `%sext_sshr_const_i32`; variant 0, row 19 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [16](artifact-mismatch-sample-96/cases/16.json) | `isa/aarch64/condbr.clif` / `%i128_bricmp_uge`; variant 0, row 24 | i128 legalization and instruction shapes | 12/48 | Stock uses CMP/SBCS for a wide compare; Lean materializes separate boolean tests and retains same-destination branches. |
| [17](artifact-mismatch-sample-96/cases/17.json) | `runtests/atomic-rmw-subword-little.clif` / `%atomic_rmw_xchg_little_i16`; variant 1, row 40 | Callee saves and stack-frame layout | 76/100 | Exchange body is similar but Lean also saves unused x28 and shifts local storage by 48 bytes; stock uses paired saves. |
| [18](artifact-mismatch-sample-96/cases/18.json) | `runtests/atomic-rmw-subword-little.clif` / `%atomic_rmw_umax_i8_reduced_operand`; variant 0, row 45 | Callee saves and stack-frame layout | 88/104 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [19](artifact-mismatch-sample-96/cases/19.json) | `isa/aarch64/amodes.clif` / `%f8`; variant 0, row 3 | Register assignment/coalescing only | 24/24 | Stock reuses x7 throughout the address chain; Lean uses separate temporaries. This is allocation/coalescing, not a consistent global renaming. |
| [20](artifact-mismatch-sample-96/cases/20.json) | `runtests/x64-bmi1.clif` / `%blsr32`; variant 0, row 2 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [21](artifact-mismatch-sample-96/cases/21.json) | `isa/aarch64/leaf_function_detection.clif` / `%leaf_with_memory`; variant 0, row 4 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [22](artifact-mismatch-sample-96/cases/22.json) | `runtests/amode-shared-base.clif` / `%amode_zero`; variant 0, row 2 | Retained pure shifts/extensions/constants | 40/44 | Unused MOV from zero-extension survives beside folded UXTW addressing; original extend MInst is not whitelisted. Temporary assignments and trap offsets also differ. |
| [23](artifact-mismatch-sample-96/cases/23.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_smin_i64`; variant 0, row 32 | Callee saves and stack-frame layout | 88/104 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [24](artifact-mismatch-sample-96/cases/24.json) | `runtests/icmp-slt.clif` / `%icmp_slt_i16_imm`; variant 0, row 5 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [25](artifact-mismatch-sample-96/cases/25.json) | `runtests/atomic-rmw-subword-little.clif` / `%atomic_rmw_smax_little_i16`; variant 0, row 36 | Callee saves and stack-frame layout | 96/112 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [26](artifact-mismatch-sample-96/cases/26.json) | `isa/aarch64/shift-rotate.clif` / `%f32`; variant 0, row 34 | Retained pure shifts/extensions/constants | 12/16 | Unused LSL survives after folding into SBFX and shifted ADD; shift op is excluded from pureAlu. |
| [27](artifact-mismatch-sample-96/cases/27.json) | `isa/aarch64/condops-with-csdb.clif` / `%f`; variant 0, row 10 | Repeated comparison/boolean materialization | 12/20 | Unused CMP/CSET precedes re-comparison for CSEL. Neither stream emits CSDB despite the filename. |
| [28](artifact-mismatch-sample-96/cases/28.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_smin_i64_no_res`; variant 0, row 33 | Callee saves and stack-frame layout | 84/100 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [29](artifact-mismatch-sample-96/cases/29.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_xchg_i64_no_res`; variant 0, row 41 | Callee saves and stack-frame layout | 68/92 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [30](artifact-mismatch-sample-96/cases/30.json) | `runtests/icmp.clif` / `%test_ult_ugt`; variant 0, row 10 | Register assignment/coalescing only | 24/24 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [31](artifact-mismatch-sample-96/cases/31.json) | `wasm/i64-compares.clif` / `%i64_ge_s`; variant 0, row 9 | Repeated comparison/boolean materialization | 12/20 | Lean repeats CMP/CSET while widening the comparison boolean; stock emits one pair. |
| [32](artifact-mismatch-sample-96/cases/32.json) | `isa/aarch64/amodes.clif` / `%f5`; variant 0, row 0 | Retained pure shifts/extensions/constants | 8/12 | Unused SXTW remains beside folded SXTW LDR addressing; extra code moves the trap offset. |
| [33](artifact-mismatch-sample-96/cases/33.json) | `isa/aarch64/condops-with-csdb.clif` / `%f`; variant 0, row 13 | Repeated comparison/boolean materialization | 12/20 | Lean materializes a comparison boolean and repeats comparison for its selected consumer; stock avoids the extra materialization. Flag-setting/reading forms are outside cleanup coverage. |
| [34](artifact-mismatch-sample-96/cases/34.json) | `runtests/issue5901.clif` / `%a`; variant 0, row 0 | Callee saves and stack-frame layout | 92/108 | Compare-and-swap body forms agree; save strategy, local-stack and branch offsets and a constant register differ. |
| [35](artifact-mismatch-sample-96/cases/35.json) | `runtests/fold-bitops.clif` / `%simplify_bor_xyy`; variant 0, row 3 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [36](artifact-mismatch-sample-96/cases/36.json) | `isa/aarch64/atomic-rmw.clif` / `%atomic_rmw_smin_i8`; variant 0, row 35 | Callee saves and stack-frame layout | 72/96 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [37](artifact-mismatch-sample-96/cases/37.json) | `isa/aarch64/amodes.clif` / `%f9`; variant 0, row 4 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [38](artifact-mismatch-sample-96/cases/38.json) | `isa/aarch64/bmask.clif` / `%bmask_i128_i64`; variant 0, row 17 | i128 legalization and instruction shapes | 16/40 | Stock ORRs the i128 halves and uses CSETM; Lean compares both halves then selects explicit all-ones/zero constants. |
| [39](artifact-mismatch-sample-96/cases/39.json) | `runtests/i128-bitrev.clif` / `%bitrev_i128`; variant 0, row 3 | Instruction order | 16/16 | Both have MOV and two RBIT instructions, but preserve/reverse opposite halves first. Instruction order differs; not register-only correspondence by position. |
| [40](artifact-mismatch-sample-96/cases/40.json) | `runtests/shifts.clif` / `%rotl_zero_left_operand`; variant 0, row 75 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [41](artifact-mismatch-sample-96/cases/41.json) | `runtests/select.clif` / `%select_eq_zero_isub`; variant 0, row 49 | Repeated comparison/boolean materialization | 20/28 | Unused CMP/CSET precedes the comparison fused into CSEL; live arithmetic/constant temporary registers also differ. |
| [42](artifact-mismatch-sample-96/cases/42.json) | `runtests/arithmetic.clif` / `%fold_isub_iadd_band_to_bor_i32_rt`; variant 0, row 46 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [43](artifact-mismatch-sample-96/cases/43.json) | `runtests/i128-call.clif` / `%callee_i128`; variant 1, row 0 | i128 legalization and instruction shapes | 20/48 | Stock uses ADDS/ADC; Lean expands carry to CMP/CSET and additions, with copy and duplicated boolean materialization. |
| [44](artifact-mismatch-sample-96/cases/44.json) | `runtests/srem_opts.clif` / `%srem_larger_divisor_negative_i64`; variant 0, row 24 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [45](artifact-mismatch-sample-96/cases/45.json) | `runtests/i128-load-store.clif` / `%i128_stack_store_load`; variant 0, row 0 | i128 legalization and instruction shapes | 52/60 | Stock uses paired i128 memory operations and CMP/CCMP; Lean uses separate memory operations and CSET booleans combined with AND. Mixed causes. |
| [46](artifact-mismatch-sample-96/cases/46.json) | `isa/aarch64/atomic-rmw.clif` / `%atomic_rmw_and_i8`; variant 0, row 11 | Callee saves and stack-frame layout | 64/88 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [47](artifact-mismatch-sample-96/cases/47.json) | `runtests/i128-load-store.clif` / `%i128_store_load_offset`; variant 0, row 4 | i128 legalization and instruction shapes | 48/60 | Same paired-memory/wide-equality difference as case 45 at nonzero offsets; traps differ in offsets and access-site structure. |
| [48](artifact-mismatch-sample-96/cases/48.json) | `isa/aarch64/uextend-sextend.clif` / `%f_u_icmp_32`; variant 0, row 12 | Repeated comparison/boolean materialization | 12/20 | Lean materializes a comparison boolean and repeats comparison for its selected consumer; stock avoids the extra materialization. Flag-setting/reading forms are outside cleanup coverage. |
| [49](artifact-mismatch-sample-96/cases/49.json) | `runtests/integer-minmax.clif` / `%smin_max_i32`; variant 0, row 3 | Register assignment/coalescing only | 24/24 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [50](artifact-mismatch-sample-96/cases/50.json) | `runtests/i128-icmp.clif` / `%icmp_imm_ne_i128`; variant 0, row 11 | i128 legalization and instruction shapes | 32/52 | Fresh copies and separate high/low inequality booleans replace stock CMP/CCMP wide comparison. |
| [51](artifact-mismatch-sample-96/cases/51.json) | `runtests/selectif-spectre-guard.clif` / `%select_spectre_guard_i128_sle`; variant 0, row 24 | Repeated comparison/boolean materialization | 24/48 | Stock shares signed-byte comparison across two CSELs; Lean materializes an unused boolean and repeats comparison/extension for each half. |
| [52](artifact-mismatch-sample-96/cases/52.json) | `runtests/i128-shifts.clif` / `%ishl_i32_i128`; variant 0, row 6 | i128 legalization and instruction shapes | 8/12 | Explicit AND #31 masks the low part of an i128 shift count; stock uses the low word directly. |
| [53](artifact-mismatch-sample-96/cases/53.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_or_i64_no_res`; variant 0, row 13 | Callee saves and stack-frame layout | 80/96 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [54](artifact-mismatch-sample-96/cases/54.json) | `runtests/arithmetic.clif` / `%test_ule_x_umax`; variant 0, row 66 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [55](artifact-mismatch-sample-96/cases/55.json) | `runtests/srem_opts.clif` / `%srem_pow2_pattern_test2_i64`; variant 0, row 26 | Register assignment/coalescing only | 32/32 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [56](artifact-mismatch-sample-96/cases/56.json) | `runtests/select.clif` / `%select_icmp_eq_zero`; variant 0, row 13 | Repeated comparison/boolean materialization | 12/20 | Unused CMP-immediate/CSET precedes comparison against XZR for CSEL; stock emits only the latter comparison. |
| [57](artifact-mismatch-sample-96/cases/57.json) | `runtests/srem_opts.clif` / `%const_srem_large_i64`; variant 0, row 16 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [58](artifact-mismatch-sample-96/cases/58.json) | `runtests/i128-bitcast.clif` / `%bitcast_i128_i128`; variant 0, row 0 | i128 legalization and instruction shapes | 4/12 | Two live ORR identity copies for i128 bitcast survive while stock emits only RET; deadness alone cannot remove live outputs. |
| [59](artifact-mismatch-sample-96/cases/59.json) | `runtests/arithmetic.clif` / `%test_iadd_smin_smax`; variant 0, row 53 | Register assignment/coalescing only | 24/24 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [60](artifact-mismatch-sample-96/cases/60.json) | `isa/aarch64/uextend-sextend.clif` / `%f_u_icmp_64`; variant 0, row 13 | Repeated comparison/boolean materialization | 12/20 | Lean materializes a comparison boolean and repeats comparison for its selected consumer; stock avoids the extra materialization. Flag-setting/reading forms are outside cleanup coverage. |
| [61](artifact-mismatch-sample-96/cases/61.json) | `isa/aarch64/bitops.clif` / `%band_i64_constant_shift2`; variant 0, row 43 | Retained pure shifts/extensions/constants | 8/12 | Unused LSL survives before shifted-register AND. Shift operation is outside pureAlu whitelist. |
| [62](artifact-mismatch-sample-96/cases/62.json) | `runtests/bitops.clif` / `%test_uge_x_band`; variant 0, row 62 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [63](artifact-mismatch-sample-96/cases/63.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_and_i64_no_res`; variant 0, row 9 | Callee saves and stack-frame layout | 80/96 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [64](artifact-mismatch-sample-96/cases/64.json) | `runtests/atomic-rmw-subword-little.clif` / `%atomic_rmw_xchg_little_i16_no_res`; variant 1, row 41 | Callee saves and stack-frame layout | 72/96 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [65](artifact-mismatch-sample-96/cases/65.json) | `isa/aarch64/atomic_load.clif` / `%atomic_load_i8_i64`; variant 0, row 6 | Atomic-load extension folding | 8/12 | Stock LDARB writes the result directly; Lean emits LDARB then UXTB. Disabled sinking prevents atomic-load/extension combination. |
| [66](artifact-mismatch-sample-96/cases/66.json) | `runtests/arithmetic.clif` / `%test_ugt_x_umax`; variant 0, row 80 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [67](artifact-mismatch-sample-96/cases/67.json) | `runtests/arithmetic.clif` / `%imul_small_constant`; variant 0, row 37 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [68](artifact-mismatch-sample-96/cases/68.json) | `runtests/integer-minmax.clif` / `%smin_max_i8`; variant 0, row 1 | Register assignment/coalescing only | 32/32 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [69](artifact-mismatch-sample-96/cases/69.json) | `isa/aarch64/uextend-sextend.clif` / `%f_u_icmp_i128`; variant 0, row 15 | i128 legalization and instruction shapes | 16/40 | Stock uses CMP/SBCS/CSET for wide unsigned comparison; Lean combines separate half less/equality booleans. |
| [70](artifact-mismatch-sample-96/cases/70.json) | `isa/aarch64/extr.clif` / `%a64_extr_i32_12_swap`; variant 0, row 1 | Retained pure shifts/extensions/constants | 8/16 | Unused LSL/LSR survive before EXTR; both standalone shifts are outside the whitelist. |
| [71](artifact-mismatch-sample-96/cases/71.json) | `isa/aarch64/uextend-sextend.clif` / `%f_u_icmp_i128_out`; variant 0, row 19 | Repeated comparison/boolean materialization | 20/24 | Repeated CMP/CSET while extending a boolean to i128; stock additionally has explicit UXTB on the low half. Both emit high-half zero. |
| [72](artifact-mismatch-sample-96/cases/72.json) | `runtests/shifts.clif` / `%sshr_zero_left_operand`; variant 0, row 80 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [73](artifact-mismatch-sample-96/cases/73.json) | `isa/aarch64/symbol-value-pic.clif` / `%colocated_symbol_value_minus_offset`; variant 0, row 7 | Register assignment/coalescing only | 20/20 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [74](artifact-mismatch-sample-96/cases/74.json) | `isa/aarch64/shift-rotate.clif` / `%f30`; variant 0, row 32 | Retained pure shifts/extensions/constants | 8/12 | Unused LSL survives alongside SBFIZ folding the shift/extension expression. |
| [75](artifact-mismatch-sample-96/cases/75.json) | `runtests/icmp.clif` / `%fold_cmp_over_nots2`; variant 0, row 4 | Register assignment/coalescing only | 24/24 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [76](artifact-mismatch-sample-96/cases/76.json) | `runtests/select.clif` / `%select_icmp64_slt_imm`; variant 0, row 20 | Repeated comparison/boolean materialization | 12/20 | Lean materializes a comparison boolean and repeats comparison for its selected consumer; stock avoids the extra materialization. Flag-setting/reading forms are outside cleanup coverage. |
| [77](artifact-mismatch-sample-96/cases/77.json) | `runtests/extend.clif` / `%add_sextend16_32`; variant 0, row 20 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [78](artifact-mismatch-sample-96/cases/78.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_sub_i32_no_res`; variant 0, row 7 | Callee saves and stack-frame layout | 80/96 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [79](artifact-mismatch-sample-96/cases/79.json) | `isa/aarch64/condops-with-csdb.clif` / `%f`; variant 0, row 15 | Repeated comparison/boolean materialization | 12/20 | Lean materializes a comparison boolean and repeats comparison for its selected consumer; stock avoids the extra materialization. Flag-setting/reading forms are outside cleanup coverage. |
| [80](artifact-mismatch-sample-96/cases/80.json) | `isa/aarch64/narrow-arithmetic.clif` / `%add32_8`; variant 0, row 3 | Retained pure shifts/extensions/constants | 8/12 | Unused SXTB survives alongside ADD with built-in SXTB operand. |
| [81](artifact-mismatch-sample-96/cases/81.json) | `runtests/i128-shifts.clif` / `%sshr_i8_i128`; variant 0, row 26 | i128 legalization and instruction shapes | 16/20 | Lean masks the low i128 shift count twice using 64-bit operations; stock uses one 32-bit mask. Both perform narrow arithmetic shift/sign extension. |
| [82](artifact-mismatch-sample-96/cases/82.json) | `isa/aarch64/extr.clif` / `%a64_extr_i32_12`; variant 0, row 0 | Retained pure shifts/extensions/constants | 8/16 | Unused LSR/LSL remain before EXTR; shifts are outside the whitelist. |
| [83](artifact-mismatch-sample-96/cases/83.json) | `runtests/bitops.clif` / `%test_bor_bxor_bxor_x`; variant 0, row 28 | Register assignment/coalescing only | 16/16 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [84](artifact-mismatch-sample-96/cases/84.json) | `runtests/rotl.clif` / `%rotl_i64_i128`; variant 0, row 16 | i128 legalization and instruction shapes | 12/20 | Fresh low-half copy and explicit count mask precede NEG/ROR; stock uses the low count register directly. |
| [85](artifact-mismatch-sample-96/cases/85.json) | `runtests/atomic-rmw-little.clif` / `%atomic_rmw_smax_i32`; variant 0, row 38 | Callee saves and stack-frame layout | 88/104 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [86](artifact-mismatch-sample-96/cases/86.json) | `isa/aarch64/condops.clif` / `%f`; variant 0, row 5 | Repeated comparison/boolean materialization | 16/28 | Lean emits UXTH/CMP/CSET then repeats UXTH/CMP for CSEL; stock emits only the selected comparison. |
| [87](artifact-mismatch-sample-96/cases/87.json) | `isa/aarch64/icmp-const.clif` / `%f`; variant 0, row 5 | Retained pure shifts/extensions/constants | 12/20 | Unused MOV/MOVK constant construction remains despite CMP shifted immediate. movK is excluded from pureForm and its input keeps the first constant live. |
| [88](artifact-mismatch-sample-96/cases/88.json) | `runtests/bitops.clif` / `%test_aarch64_extr`; variant 0, row 60 | Retained pure shifts/extensions/constants | 12/16 | Unused LSR-by-zero on first input remains; both streams contain the second input's LSR-by-zero. Shifts are not whitelisted. |
| [89](artifact-mismatch-sample-96/cases/89.json) | `runtests/i128-shifts.clif` / `%ishl_i128_i32`; variant 0, row 2 | i128 legalization and instruction shapes | 40/88 | Wide shift expands to masks/comparisons/selects; stock uses a shorter cross-half shift/merge and bit-test sequence. Not dead code alone. |
| [90](artifact-mismatch-sample-96/cases/90.json) | `isa/aarch64/condops-with-csdb.clif` / `%f`; variant 0, row 18 | Repeated comparison/boolean materialization | 12/20 | Lean materializes a comparison boolean and repeats comparison for its selected consumer; stock avoids the extra materialization. Flag-setting/reading forms are outside cleanup coverage. |
| [91](artifact-mismatch-sample-96/cases/91.json) | `isa/aarch64/atomic-rmw-lse.clif` / `%atomic_rmw_nand_i8`; variant 0, row 15 | Callee saves and stack-frame layout | 68/92 | Lean uses individual STUR/LDUR saves/restores inside a separately allocated frame; stock uses paired/pre-post-indexed saves. LL/SC body forms agree; layout changes branch/trap offsets, with possible temporary-register differences. |
| [92](artifact-mismatch-sample-96/cases/92.json) | `runtests/i128-arithmetic-extends.clif` / `%sext_sshr_i32_i128`; variant 0, row 0 | i128 legalization and instruction shapes | 12/16 | AND #31 on low i128 count precedes narrow ASR/extension; stock relies on hardware masking. |
| [93](artifact-mismatch-sample-96/cases/93.json) | `runtests/fold-bitops.clif` / `%test_bxor_band_bnot_x`; variant 0, row 8 | Register assignment/coalescing only | 12/12 | Same instruction/operand shapes, immediates and widths; register assignments/reuse differ. Token masking is a diagnostic only; exact verdicts remain literal. |
| [94](artifact-mismatch-sample-96/cases/94.json) | `isa/aarch64/dead-notrap-load.clif` / `%dead_notrap_load`; variant 0, row 0 | Unused nontrapping load | 4/8 | Unused notrap/aligned source load remains as LDR; stock emits RET only. Cleanup deliberately excludes memory. |
| [95](artifact-mismatch-sample-96/cases/95.json) | `isa/aarch64/amodes.clif` / `%f6`; variant 0, row 1 | Retained pure shifts/extensions/constants | 8/12 | Unused SXTW precedes folded SXTW LDR, also moving its trap offset. |
| [96](artifact-mismatch-sample-96/cases/96.json) | `isa/aarch64/extr.clif` / `%a64_extr_i64_12`; variant 0, row 4 | Retained pure shifts/extensions/constants | 8/16 | Unused 64-bit LSR/LSL remain before EXTR; same retained-shift pattern as cases 70/82. |

### Reproduce and verify

With an isolated Python environment containing `capstone==5.0.9`:

```sh
gh run download 38093345756 --name stock-comparison-artifacts-1 --dir /tmp/sample96-download
mkdir -p /tmp/sample96-extracted
tar -xzf /tmp/sample96-download/stock-comparison-artifacts.tar.gz -C /tmp/sample96-extracted
python docs/research/artifact-mismatch-sample-96/reproduce.py /tmp/sample96-extracted/target/ci-comparison /tmp/sample96-evidence
python docs/research/artifact-mismatch-sample-96/verify.py /tmp/sample96-extracted/target/ci-comparison /tmp/sample96-evidence
```

The artifact verifier requires this matching compiler-source checkout. The sample
was generated with Python 3.14 and Capstone 5.0.9. `classification.json` is the
manual source/stream assessment and is retained separately from evidence generation.


## Historical investigation: 32 pre-cleanup occurrences

This section retains the full original case-by-case investigation and its methods.
Case numbers here are **historical 01–32**. Source locations, provenance and statements
about the checkout refer to the recorded October 5 revision, not current main;
historical snapshot verification must use that source revision. Its counts are
not estimates for today's remaining population. The later cleanup explicitly gained
historical cases 9, 13, 22 and 25 in its paired receipt; absence from that gain list
alone is not a complete recheck of all other historical cases.

A random sample of 32 nonmatching stock Cranelift and Lean function artifacts
shows that most differences arise from instruction emission and register choice.
Seventeen cases retain unused instructions after a consumer folds their source
operation, and nine differ only in consistently assigned temporary registers.
The remaining six involve i128 legalization, an atomic-load extension, or
callee-save layout. The three differing trap records identify the corresponding
memory instructions at their new offsets. These observations explain the exact
artifact verdicts; this investigation did not run the generated functions or
establish semantic equivalence.

The report diagnoses every selected occurrence below. Its
[evidence manifest](artifact-mismatch-sample/manifest.json) and 32 linked case
snapshots preserve inputs, literal machine bytes, disassembly, settings receipts,
relocations, alignment, trap records, and compiler metadata.

### Measurement and random selection

The source is the completed [comparison run of October 5, 2026](https://github.com/eth-act/clifv/actions/runs/37265516388),
artifact `stock-comparison-artifacts-1`, ID `11326645935`. The checkout was
`c8e1bdec10881f66700846b622a32cf54ce36fbf`; the pinned stock Wasmtime revision was
`46c23a87dac1465986a8ad53ba6a7ae49372857b` (Cranelift 0.136.1).
The archived report inventories all 1,302 official files and reports 4,501
function compilation occurrences: 983 `different_code_artifact`, 425
`identical_code_artifact`, 1,871 `lean_unsupported`, 1,176
`unsupported_configuration`, and 46 expected stock rejections without binaries.

The sampling population is **all 983 `different_code_artifact` occurrences**:
both compilers produced artifacts under an accepted settings contract.
Unsupported settings, missing Lean outputs, foreign-target files, and unknown
execution metadata are separate coverage questions, outside this sampling
population. This is a sample of comparisons, not 32 distinct official files.
The draw contains 32 distinct function occurrences across 21 files: 22 `run`
stage captures and 10 `compile` stage captures. A captured `run` stage compiles
the prepared functions; it does not execute runtime assertions.

Each population entry is `(test path, variant index, function name, comparison
row index)`. The row index distinguishes repeated reported names without
discarding any occurrence. Sort these entries lexicographically, then draw
without replacement using Python 3.12:

```python
random.Random(15736773078534225743).sample(sorted(population), 32)
```

The seed was one `secrets.randbits(64)` draw before inspecting the selected
diagnoses. There was no redraw, filtering by diagnosis, or replacement of
difficult cases. The manifest preserves the complete population and draw order,
the original `results.json` SHA256, compiler binary hashes, and source hashes.
Disassembly uses Capstone 5.0.9, AArch64 little endian, with address zero. The
bytes remain unmodified; symbol relocations remain unresolved.

Three `gpt-6-luna` agents analyzed disjoint batches (1–11, 12–22, and 23–32).
The coordinating agent inspected all 32 instruction streams and reviewed the
findings against the saved settings, metadata, and compiler sources.

### Findings across the sample

The categories below are mutually exclusive primary explanations. Secondary
effects, such as different temporary registers or moved trap offsets, are
included in the individual diagnoses.

| Primary explanation | Cases | Count |
| --- | --- | ---: |
| Folded producers still emitted as unused instructions | 1, 4, 6, 9, 10, 12, 13, 14, 16, 20, 21, 22, 25, 26, 28, 31, 32 | 17 |
| Temporary register choice only | 2, 3, 5, 8, 15, 17, 24, 29, 30 | 9 |
| Larger sequences from i128 legalization and control lowering | 11, 18, 23, 27 | 4 |
| Atomic load and extension selected separately | 7 | 1 |
| Different layout and instructions for saving callee-saved registers | 19 | 1 |

All 32 differ in literal code bytes. Relocations and required alignment match
in every case. Trap records match in 29; cases 1, 14, and 19 have the same trap
kinds at different instruction offsets. Every sampled stock stage repeats
identically, and every Lean dump agrees with its ELF object's function bytes,
relocations, and alignment. None of these mismatches is attributable to a
rejected settings receipt or a dump/object inconsistency.

Stock code totals 512 bytes across the sample; Lean totals 752, an additional
240 bytes (46.9%). Lean is larger in 23 cases and the same size in nine; it is
smaller in none. These figures describe this draw and are not an estimate of
whole-suite code size or performance.

#### Why folded instructions remain

This is directly supported by the implementation. The Lean driver documents
that it lowers every instruction top-down, including dead pure instructions,
while Cranelift lowers bottom-up so it can skip definitions no longer needed
after selecting their consumers
([Isel.lean](../../FV/Backend/Isel.lean), lines 18–26 and 1152–1174).
Consequently, Lean often selects the **same fused instruction** as stock but
has already emitted the absorbed constant, complement, multiply, comparison,
or address calculation. Calling these cases a missing fusion would obscure the
actual problem: the fusion succeeds and its unused producer survives.

The corresponding pinned stock driver checks `must_lower || value_needed`
before generating code and can reuse opportunistic definitions
(`third_party/wasmtime/cranelift/codegen/src/machinst/lower.rs`, lines 880–925).
Lean's `opportunistic_def` is a no-op and `is_sinkable_inst` fails
([Isel.lean](../../FV/Backend/Isel.lean), lines 771 and 788).
Register-only cases show different allocation outcomes; these artifacts do not
identify one particular allocator heuristic as their cause.

### Attribution to Lean implementation gaps and correctness fixes

The sample establishes code-generation quality gaps, but it supplies no
demonstrated Lean wrong-code counterexample. A mismatch alone does not establish
a correctness defect. The following table attributes every case to the relevant
implementation decision and separates avoidable extra code from ordinary
allocation variation.

| Attribution | Cases | Lean implementation responsible | Assessment |
| --- | --- | --- | --- |
| Retained pure producers after folding | 1, 4, 6, 9, 10, 12, 13, 14, 16, 20, 21, 22, 25, 26, 28, 31, 32 | `Backend.lowerFunction` in `FV/Backend/Isel.lean:1152`, which emits each instruction without a needed-value check; top-down traversal documented at line 22 | Concrete missed optimizations: the fused consumer exists, but its unused producers survive. This deliberate simplification dates to the original driver, commit `41b3e98`; it is not documented as a bug fix. |
| Atomic load extension combination disabled | 7 | `externCtor` in `FV/Backend/Isel.lean:788`: `is_sinkable_inst` always fails | Concrete missed optimization. The stock combination requires sinkability; Lean falls back to LDARH plus explicit UXTH. No correctness fix explains the extra instruction. |
| i128 legalization produces a larger live representation | 11, 18, 23, 27 | `Pat.copy2`, `Pat.shiftNarrow`, `Pat.bmask128c`, and `Pat.icmp` in `FV/Opt/Legal.lean:261,305,331,336`; pattern emission in `FV/Opt/Legalize128Pass.lean:71` | Deliberate canonical expansions with optimization opportunities: extra copies/masks, repeated mask construction, or separate boolean comparisons. Case 27 also keeps a same-destination branch through `lowerFunction`. These are not evidence of incorrect i128 semantics. |
| Individual callee saves instead of paired saves | 19 | `RAFrame.compute` in `FV/Backend/Regalloc.lean:225`, individual save/reload lowering, and `prologueLines` in `FV/Backend/Asm.lean:430` | A less compact frame-emission strategy. The atomic loop itself matches stock; the extra frame instructions explain the code and trap-offset differences. |
| Physical register choices | 2, 3, 5, 8, 15, 17, 24, 29, 30 | Virtual-register construction, aliasing, and subsequent `regalloc2` allocation | Ordinary implementation variation, not an identified defect. The defining and consuming operands are consistently renamed. The exact heuristic responsible was not isolated. |

Thus 18 cases have direct missed optimizations in the lowering driver, five
have less compact legalization or frame strategies, and nine have ordinary
register-choice differences. The first two groups account for the 23 larger
Lean outputs. Calling all 32 Lean defects would incorrectly count the nine
register-only cases as bugs. Calling the other 23 correctness bugs would also
go beyond the evidence.

#### Which differences trace to a correctness related change

**Cases 11 and 23 have a partial historical explanation related to validation.**
Commit [a848be2](https://github.com/eth-act/clifv/commit/a848be2744dab3b33738f239570de066d4402783)
replaced aliases for `iconcat` and related operations with explicit `bor x,x`
copies. Its source comment explains that each i128 value receives its own fresh
pair to satisfy the validator's injectivity requirement. The sampled copies
`orr x6,x1,x1` and `orr x8,x2,x2` implement exactly that pattern. The low copy
is consumed; the high copy is unused in these narrow shift/rotate cases.
This explains part of their extra code as a validation-driven representation
change, not evidence that stock's direct use of the low half is wrong. The
commit does not establish an earlier wrong-code counterexample for these two
sampled functions. Removing emitted dead copies or coalescing live copies can
be investigated while retaining fresh identities in the legalization proof.

**No sampled mismatch was identified as a necessary fix for a stock compiler
bug.** The documented deliberate divergence is `atomic_cas.i32`: Lean compares
the expected operand with `uxtw`, while the pinned stock backend wrongly
compares its unspecified upper register bits
([Asm.lean](../../FV/Backend/Asm.lean), lines 273–283;
[upstream bug report](upstream-bugs.md)). None of the sampled source functions
contains `atomic_cas`. Case 19 uses `atomic_rmw.i8 umin`; its comparison and
retry loop match stock exactly. Although commit
[7365bf2](https://github.com/eth-act/clifv/commit/7365bf242f989baeef0b3cb4ad662068db55a6e3)
also repaired Lean atomic lowering, that repaired loop is the matching portion
of case 19, not the cause of its remaining mismatch.

The other documented upstream bug concerns out-of-range shifts in mid-end
rewrite rules. Every selected receipt requests `opt_level=none`; the stock
adapter forbids an independent `--opt` override. Those optimizer fixes do not
explain this sample. Case 1's historical regression filename is likewise not
evidence of an intentional divergence: both emitted accesses use the correct
shift of 17.

### Individual diagnoses

Sizes below are stock → Lean in bytes. Instruction offsets are hexadecimal;
trap metadata offsets are decimal. Each evidence link includes both complete
instruction streams and the source function.

#### Case 1 Address calculation before a narrow load

`isa/aarch64/issue-shift-masked-imm-type.clif`,
`%load_i16_ishl17_should_not_fold`, variant 0, 12 → 20 bytes.
Both streams shift the index by **17** and load from base plus shifted index.
Lean additionally emits unused `mov x3,#17` at `0x00` and
`add x7,x0,x1,lsl #17` at `0x08`; the load uses `x5`, not `x7`.
The final index therefore retains the required shift; this is not evidence of
the historical shift-count masking bug named by the test. `heap_oob` moves from
offset 4 to 12, exactly with `ldrh`. The primary cause is retained folded
producers, with register choice and trap-PC movement as secondary differences.
[Evidence](artifact-mismatch-sample/cases/01.json).

#### Case 2 Temporaries in three logical operations

`runtests/bitops.clif`, `%test_bxor_bor_band_i64`, variant 0, 16 → 16 bytes.
Both emit `orr`, `and`, `eor`, and `ret` in the same order. Stock puts the first
two results in `x5/x6`; Lean uses `x3/x5`. Their `eor` at `0x08` reads those
respective results and writes `x0`. Consistent temporary register assignment
accounts for every code difference; no instruction is added or removed.
[Evidence](artifact-mismatch-sample/cases/02.json).

#### Case 3 Temporary in signed extension of subtraction

`runtests/arithmetic-extends.clif`, `%sext_sub_i32`, variant 0, 12 → 12 bytes.
Stock's `sub w4,w0,w1` and `sxtw x0,w4` become Lean's `sub w3,w0,w1` and
`sxtw x0,w3`, at `0x00/0x04`. The same 32-bit subtraction feeds the same signed
extension into the return register. Only the temporary register changes.
[Evidence](artifact-mismatch-sample/cases/03.json).

#### Case 4 Unused complement before a fused bit clear

`runtests/bitops.clif`, `%test_band_band_bnot_x_y_x`, variant 0, 12 → 16 bytes.
Lean's `mvn w3,w0` at `0x00` is unused: the next instruction already computes
the complemented AND through `bic w5,w1,w0`. Stock emits that BIC directly
into `w4`. Both then AND its result with the original `w0`; the expression
`(~x & y) & x` is zero. The extra complement survives despite successful BIC
selection. Neither compiler folds the whole expression to zero in this
configuration.
[Evidence](artifact-mismatch-sample/cases/04.json).

#### Case 5 Register holding a zero shift operand

`runtests/shifts.clif`, `%sshr_zero_left_operand`, variant 0, 12 → 12 bytes.
Stock materializes zero in `x3`; Lean uses `x2`. Their variable `asr` at `0x04`
reads that zero and the same count in `x0`, then returns in `x0`. All operations
and widths match. The mismatch is only the zero's allocated register; both
retain the shift operation.
[Evidence](artifact-mismatch-sample/cases/05.json).

#### Case 6 Divisor materialized twice for signed remainder

`runtests/srem_opts.clif`, `%const_srem_imm_pow2_i64`, variant 0, 20 → 24 bytes.
Both compute `1000 % 16` with `sdiv` followed by `msub`. Lean retains
`mov x3,#16` at `0x04`, then materializes the divisor again in `w5` at `0x08`;
only `x5` feeds the divide and remainder calculation. Stock materializes it
once in `w1`. The first Lean divisor definition is unused. Requested
`opt_level=none` also explains why neither stream replaces the entire arithmetic
calculation with its constant result.
[Evidence](artifact-mismatch-sample/cases/06.json).

#### Case 7 Explicit extension after an atomic halfword load

`isa/aarch64/atomic_load.clif`, `%atomic_load_i16_i64`, variant 0, 8 → 12 bytes.
Stock emits `ldarh w0,[x0]` and returns. Lean emits `ldarh w2,[x0]` at `0x00`
and `uxth w0,w2` at `0x04`. The load already clears upper bits, so the extension
is redundant but copies the result to `w0`. The pinned rule for combining
`uextend(atomic_load)` requires `is_sinkable_inst`
(`third_party/wasmtime/cranelift/codegen/src/isa/aarch64/lower.isle`, lines
1270–1274); Lean's failing helper prevents that rule from matching. This is a
missing load/extension combination, distinct from an unused emitted producer.
Both trap records identify `heap_oob` at offset 0.
[Evidence](artifact-mismatch-sample/cases/07.json).

#### Case 8 Temporaries in an eight bit select

`runtests/select.clif`, `%select_x_one_borxy_to_select_x_one_y_rt`, variant 0,
20 → 20 bytes. Both materialize 1, OR the arguments, test `w0` with mask
`#0xff`, and use `csel ... ne`. Stock uses `w5/w6` for the alternatives;
Lean uses `w3/w5`. The `csel` at `0x0c` consumes those consistently renamed
values. Only temporary register choices differ.
[Evidence](artifact-mismatch-sample/cases/08.json).

#### Case 9 Unused constants around an i128 signed extension

`isa/aarch64/extend-op.clif`, `%i128_sextend_i8`, variant 0, 12 → 20 bytes.
Both live sequences are exactly `sxtb x0,w0` and `asr x1,x0,#63`, producing
the low and sign-filled high halves. Lean also emits unused `mov x2,#0` at
`0x00` and `mov x6,#63` at `0x08`. Its legalization supplies the shift constant
([Legal.lean](../../FV/Opt/Legal.lean), lines 320–324), but the live ASR uses an
immediate. The primary artifact difference is the surviving constants, rather
than a different live result calculation.
[Evidence](artifact-mismatch-sample/cases/09.json).

#### Case 10 Constant retained beside an immediate addition

`runtests/global_value.clif`, `%load_at_0_and_add`, variant 0, 12 → 16 bytes.
Both load through `x0` and add immediate `#1`. Lean additionally emits unused
`mov x4,#1` at `0x04`; its ADD at `0x08` consumes the immediate directly.
The load temporary also changes from `x3` to `x2`. The source load is `notrap`,
and both trap lists are empty. The main difference is retained constant
materialization, not global-symbol relocation.
[Evidence](artifact-mismatch-sample/cases/10.json).

#### Case 11 Expanded handling of an i128 rotate count

`runtests/rotl.clif`, `%rotl_i32_i128`, variant 0, 12 → 32 bytes.
Stock computes `neg w4,w1` and rotates `w0` with `ror`. Lean copies the low
count half to `x6`, explicitly masks it with `#31` into `x12`, negates `w12`,
and rotates. That low-half copy is **used**; the copied high half `x8` and
constants in `x4/x10` are unused. Legalization introduces copies of both halves
and an explicit width mask ([Legal.lean](../../FV/Opt/Legal.lean), lines
331–338). The mask is unnecessary for the hardware 32-bit rotate's count
reduction, while the high count half has no effect on a count modulo 32.
[Evidence](artifact-mismatch-sample/cases/11.json).

#### Case 12 Constant retained before a branch calculation

`runtests/br.clif`, `%brif_false__i32_overflow`, variant 0, 24 → 28 bytes.
Lean materializes `-1` into unused `w2` at `0x00`, then uses the same immediate
`sub w4,w0,#1` as stock. Both branch on that 32-bit result. The inserted word
moves the return-one block from `0x10` to `0x14`, and the CBNZ itself moves
from `0x04` to `0x08`; its relative displacement and encoded word stay the
same. This is retained constant emission and shifted layout, not different
overflow or branch semantics.
[Evidence](artifact-mismatch-sample/cases/12.json).

#### Case 13 Complement retained despite bit clear fusion

`isa/aarch64/bitops.clif`, `%band_not_i64`, variant 0, 8 → 12 bytes.
Stock emits `bic x0,x0,x1`. Lean emits that same BIC at `0x04`, preceded by
`mvn x3,x1` at `0x00`, whose result is unused. BIC already computes the source
`x & ~y`; the separately lowered complement remains after its consumer absorbs
it.
[Evidence](artifact-mismatch-sample/cases/13.json).

#### Case 14 Unused address calculation before an indexed load

`isa/aarch64/amodes.clif`, `%load_not_scaled64`, variant 0, 12 → 20 bytes.
Both shift the index by 2 and issue an indexed 64-bit LDR using that result.
Lean also materializes unused constant 2 and emits unused
`add x7,x0,x1,lsl #2` at `0x08`. Its load still addresses `[x0,x5]`, where
`x5 = x1 << 2`; it does not use the extra ADD. The trap remains `heap_oob`,
moving 4 → 12 with the load. Retained folded address producers explain both
the larger buffer and changed trap offset.
[Evidence](artifact-mismatch-sample/cases/14.json).

#### Case 15 Temporary for an unsigned comparison result

`runtests/icmp.clif`, `%test_ult_ugt`, variant 0, 24 → 24 bytes.
The two CMPs, `cset ... lo`, `cset ... hi`, AND, and return all match in form
and order. Only the first boolean's temporary changes: stock `x6`, Lean `x4`,
with the corresponding AND operand changed at `0x10`. The second boolean
stays in `x7`. Consistent register renaming explains the mismatch; neither
stream folds the mutually exclusive comparison results to false.
[Evidence](artifact-mismatch-sample/cases/15.json).

#### Case 16 Shift constant and extension retained after folding

`runtests/arithmetic-extends.clif`, `%add_uext_ishl_1`, variant 0, 12 → 20 bytes.
Both shift the 32-bit argument left by 1 and add it to `x0` with an extended
operand, `add ... wN,uxtw`. Lean retains unused `mov w3,#1` at `0x00` and
`mov w7,w5` at `0x08`. The live ADD at `0x0c` reads `w5` with UXTW directly,
so it does not consume the separately materialized extension in `w7`.
Both constant and extension folding succeed; their unused producers remain.
[Evidence](artifact-mismatch-sample/cases/16.json).

#### Case 17 Registers in a PIC symbol address sequence

`isa/aarch64/symbol-value-pic.clif`, `%colocated_symbol_value_plus_offset`,
variant 0, 20 → 20 bytes. The accepted request has **`is_pic=true`**. Both
streams use ADRP/LDR GOT relocations for `global0`, materialize 123, and add it
before returning. Stock uses `x0` for the loaded address and `x2` for 123;
Lean uses `x1/x3` and writes the sum to `x0`. The two relocation records have
identical offsets, kinds, target, and addend. Only register fields differ,
including the ADRP/LDR destination; this is not a PIC-policy disagreement.
[Evidence](artifact-mismatch-sample/cases/17.json).

#### Case 18 Expanded construction of an i128 boolean mask

`isa/aarch64/bmask.clif`, `%bmask_i128_i128`, variant 0, 20 → 64 bytes.
Stock ORs the input halves, compares with zero, produces one mask through
`csetm x1,ne`, and copies it to `x0`. Lean tests each half separately through
CMP/CSET, ORs the booleans, then uses two CSELs with separately materialized
zero/all-ones alternatives. It also emits two unused initial zero definitions.
This matches the explicit legalization pattern
([Legal.lean](../../FV/Opt/Legal.lean), lines 300–307), rather than stock's
shared mask construction. Algebraically, both displayed conditions test whether
either input half is nonzero; runtime and full ABI equivalence were not tested.
[Evidence](artifact-mismatch-sample/cases/18.json).

#### Case 19 Callee save layout around an atomic minimum loop

`isa/aarch64/atomic-rmw.clif`, `%atomic_rmw_umin_i8`, variant 0, 68 → 92 bytes.
The LDAXRB, unsigned compare, CSEL, STLXRB, and retry branch have identical
encoded words. Stock saves `x24–x28` using one preindexed STR and two STPs,
then restores them with matching loads. Lean reserves `0x30` bytes and uses
five individual STURs and five LDURs, followed by explicit stack adjustment.
Both also save/restore FP and LR. This follows Lean's explicit save-slot layout
([Regalloc.lean](../../FV/Backend/Regalloc.lean), lines 225–239).
The loop moves by 12 bytes: `heap_oob` offsets 28/40 become 40/52, exactly the
new LDAXRB/STLXRB sites. Trap codes and the atomic operation stay the same;
the stack layout and instruction count differ.
[Evidence](artifact-mismatch-sample/cases/19.json).

#### Case 20 Negative divisor materialized twice

`runtests/srem_opts.clif`, `%const_srem_negative_divisor_i64`, variant 0,
20 → 24 bytes. Both implement signed remainder of 17 by -5 as SDIV/MSUB.
Lean emits `mov x3,#-5` at `0x04` and again `mov x5,#-5` at `0x08`. Only `x5`
feeds SDIV/MSUB; `x3` is unused. Stock materializes the divisor once in `x1`.
The remainder formula is the same, and the retained first divisor definition
accounts for the extra instruction.
[Evidence](artifact-mismatch-sample/cases/20.json).

#### Case 21 Comparison boolean retained before a fused select

`runtests/select.clif`, `%select_zero_icmp_neq_zero`, variant 0, 16 → 24 bytes.
Stock compares `x0` with zero once and feeds the flags to CSEL. Lean emits
`cmp x0,#0` and `cset x6,ne` at `0x04/0x08`, then compares again with `xzr`
at `0x0c` before its CSEL. Nothing reads `x6`. The second compare supplies
the live condition, so the first CMP/CSET pair is retained dead condition
materialization. The zero alternative remains live in both streams.
[Evidence](artifact-mismatch-sample/cases/21.json).

#### Case 22 Constant retained beside an immediate comparison

`runtests/icmp-ne.clif`, `%icmp_ne_i64_imm`, variant 0, 12 → 16 bytes.
Both return the result of `cmp x0,#10` and `cset x0,ne`. Lean first emits
unused `mov x2,#10` at `0x00`, even though its CMP at `0x04` uses immediate
10. The following CMP/CSET/RET words are the same as stock's. The immediate
comparison succeeds while its constant producer survives.
[Evidence](artifact-mismatch-sample/cases/22.json).

#### Case 23 Expanded handling of an i128 signed shift count

`runtests/shifts.clif`, `%sshr_i16_i128`, variant 0, 16 → 36 bytes.
Stock sign-extends the i16 value, masks `w1` with 15, and shifts. Lean copies
the low count half into live `x6`, copies the unused high half into `x8`,
emits unused zero/mask constants, and masks the low half into `x12`. It then
sign-extends the operand and masks that count again before ASR at `0x1c`.
The pair-copy and width-mask legalization patterns are explicit
([Legal.lean](../../FV/Opt/Legal.lean), lines 331–338). They add work around
the same signed shift by the low four count bits; the second mask is redundant.
[Evidence](artifact-mismatch-sample/cases/23.json).

#### Case 24 Register for a large comparison constant

`runtests/icmp-eq-imm.clif`, `%icmp_imm_eq_i64`, variant 0, 16 → 16 bytes.
Both materialize `0x4444444444444444` with the same logical-immediate form,
compare it with `x0`, return `cset x0,eq`, and RET. Stock chooses `x3` for
the constant; Lean chooses `x2`, reflected in the CMP at `0x04`. This is solely
consistent temporary register choice, not a different constant encoding strategy.
[Evidence](artifact-mismatch-sample/cases/24.json).

#### Case 25 Multiply retained before fused multiply subtract

`runtests/arithmetic.clif`, `%msub_i32`, variant 0, 8 → 12 bytes.
Stock emits only `msub w0,w1,w2,w0` and RET. Lean emits the identical MSUB at
`0x04`, preceded by `mul w4,w1,w2` at `0x00`; `w4` is unused. The fused
instruction already computes the source subtraction of the product. This is
successful multiply/subtract fusion with retained dead multiply emission.
[Evidence](artifact-mismatch-sample/cases/25.json).

#### Case 26 Zero and comparison boolean retained before select

`runtests/select.clif`, `%select_icmp_eq_zero`, variant 0, 12 → 24 bytes.
Stock emits `cmp x0,xzr`, `csel x0,x1,x2,eq`, and RET. Lean eventually emits
those same live instructions at `0x0c/0x10/0x14`, but first emits unused
`mov x4,#0`, `cmp x0,#0`, and `cset x7,eq` at `0x00/0x04/0x08`.
The live comparison overwrites the earlier flags and nothing reads `x7`.
The constant and standalone comparison survive after select fusion.
[Evidence](artifact-mismatch-sample/cases/26.json).

#### Case 27 Expanded i128 equality and an unnecessary branch

`isa/aarch64/condbr.clif`, `%i128_bricmp_eq`, variant 0, 12 → 40 bytes.
Stock emits CMP/CCMP for the input halves and RET, removing the branch because
both successors are the same block. Lean legalizes equality into two CMP/CSET
pairs, ANDs the booleans, extends the result, and emits CBNZ plus B. Both
branches target RET at `0x24`. An initial zero definition is unused.
The equality expansion follows [Legal.lean](../../FV/Opt/Legal.lean), lines
261–264, and the driver forwards both `brif` targets
([Isel.lean](../../FV/Backend/Isel.lean), lines 1189–1192 and 1240–1244).
This combines a larger legalized equality representation with failure to
collapse identical branch destinations. Even stock retains its unused CMP/CCMP
here; it does not eliminate the entire condition calculation.
[Evidence](artifact-mismatch-sample/cases/27.json).

#### Case 28 Shift amount retained after immediate selection

`runtests/arithmetic-extends.clif`, `%ishl_uextend`, variant 0, 12 → 16 bytes.
Both use a W-register move to zero-extend the i32 argument, then LSL its
64-bit result by immediate 5. Lean retains unused `mov x4,#5` at `0x04`.
The live shift at `0x08` consumes immediate 5 directly; its operand temporary
also changes from stock `x3` to Lean `x2`. Constant producer retention is the
primary difference.
[Evidence](artifact-mismatch-sample/cases/28.json).

#### Case 29 Temporary in subtraction followed by addition

`runtests/arithmetic.clif`, `%fold_add_sub3`, variant 0, 12 → 12 bytes.
Stock emits `sub w4,w0,w1` then `add w0,w4,w1`; Lean uses `w3` consistently
instead of `w4`, at `0x00/0x04`. No operation or instruction count changes.
Despite the test name, neither stream removes the cancelling subtraction and
addition under these settings. The mismatch itself is only register choice.
[Evidence](artifact-mismatch-sample/cases/29.json).

#### Case 30 Temporary in complement followed by comparison

`runtests/icmp.clif`, `%ne_bnot_x_x`, variant 0, 16 → 16 bytes.
Both emit MVN, CMP against the original value, `cset x0,ne`, and RET. Stock
uses `w3` for the complement; Lean uses `w2`, including the CMP operand at
`0x04`. Consistent register renaming explains the bytes. Neither folds the
whole comparison to its constant truth value in this configuration.
[Evidence](artifact-mismatch-sample/cases/30.json).

#### Case 31 Complemented XOR retained before fused OR

`runtests/bitops.clif`, `%test_bor_band_bnot_bxor`, variant 0, 16 → 20 bytes.
Both live sequences are AND, EOR, then ORN of the AND result with the
complemented XOR result. Lean also emits `eon w7,w0,w1` at `0x08`, computing
the standalone complemented XOR. Its ORN at `0x0c` instead reads the original
XOR in `w5`, complementing it internally; `w7` is unused. ORN fusion succeeds
but the standalone complemented producer survives. Live temporaries also differ.
[Evidence](artifact-mismatch-sample/cases/31.json).

#### Case 32 Constant and shift retained before a fused OR

`isa/aarch64/bitops.clif`, `%bor_i64_constant_shift2`, variant 0, 8 → 16 bytes.
Stock emits only `orr x0,x0,x1,lsl #3` and RET. Lean emits that identical
shifted-register ORR at `0x08`, preceded by unused `mov x3,#3` and
`lsl x5,x1,#3` at `0x00/0x04`. Both source producers have already been
absorbed into the live ORR operand. Retaining them doubles this function's
code size without changing the displayed live calculation.
[Evidence](artifact-mismatch-sample/cases/32.json).

### Suggested follow up

First investigate use-aware lowering or elimination of dead selected pure
instructions. The seventeen retained-producer cases suggest this could address
multiple instruction families together. Preserve side effects, faulting loads,
atomic ordering, and the existing proof contracts when designing such a change;
this report proposes no compiler or proof modification. An i128 pass can then
target pair copies, duplicate masks, duplicated boolean-mask construction, and
same-destination branches. Case 7 specifically needs the atomic-load extension
combination; case 19 needs paired callee-save emission if matching stock's
instruction shape is desired.

The nine register-only mismatches do not show an incorrect operand assignment.
Exact agreement would require investigating allocator inputs, virtual-register
numbering, constraints, preferences, and coalescing decisions. Masking register
fields would change the comparison contract and would not fix these exact
artifact mismatches.

Keep trap comparisons literal. Cases 1, 14, and 19 are explained by their memory
instructions moving, and their recorded offsets already point to the correct
sites. A future code-size change must regenerate the offsets for the final
layout; it should not normalize them to claim byte-exact agreement.

### Verification and reproduction

The [verification record](artifact-mismatch-sample/verification.json) confirms
all 32 identities were reproduced from the full population; all original and
adapted source snapshots and literal code snapshots match the archive; all
settings receipts echo the exact requests and shared input hash; and all stock
repeats match. The comparison function was rerun against the archived stock
buffers and Lean ELF objects for every sample, reproducing every saved row.
The source hashes and full Lean source-tree hash also match this checkout.

No compiler rebuild, generated-code execution, or semantic differential test
was performed for this report. The static dataflow analysis explains the
observed mismatches and indicates no wrong-code counterexample in these cases;
it does not prove execution equivalence. Full execution metadata equivalence
also remains unverified: the harness has no comparable Lean exception-table
export and does not fully compare enabled unwind metadata. These limitations
are separate from the sampled code-artifact differences.

To regenerate the evidence in a fresh output directory, download and extract
the named artifact, then run the scripts from the repository root. The sample
capture requires Python 3.12 with `capstone==5.0.9`; the verification script
requires only the repository and Python's standard library.

```sh
gh run download 37265516388 --repo eth-act/clifv \
  --name stock-comparison-artifacts-1 --dir /tmp/sample-artifact-download
mkdir -p /tmp/sample-artifact-extracted
tar -xzf /tmp/sample-artifact-download/stock-comparison-artifacts.tar.gz \
  -C /tmp/sample-artifact-extracted
python3.12 -m venv /tmp/sample-artifact-venv
/tmp/sample-artifact-venv/bin/python -m pip install capstone==5.0.9
/tmp/sample-artifact-venv/bin/python \
  docs/research/artifact-mismatch-sample/reproduce.py \
  /tmp/sample-artifact-extracted/target/ci-comparison /tmp/sample-artifact-evidence
python3 docs/research/artifact-mismatch-sample/verify.py \
  /tmp/sample-artifact-extracted/target/ci-comparison /tmp/sample-artifact-evidence
```

The verifier requires the recorded checkout's source hashes. CI artifacts have
seven-day retention, so downloading the original full run is time-limited.
The checked-in case snapshots preserve the selected inputs and code/metadata
evidence after that download expires; they do not preserve every original ELF
object or the entire comparison archive.
