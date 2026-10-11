# Post-cleanup diagnosis of 96 sampled artifact disagreements

This sample is from main `bc3a34cf018ea024ef8df4b3bda3fde28ebd5874`, **after** the
legacy-driver dead-instruction cleanup in #137. It classifies 96 randomly selected
stock/Lean function-compilation occurrences. All 96 source snapshots and both
instruction streams were inspected; preserved evidence includes literal code,
disassembly, relocations, alignment, traps, original/adapted input, and settings
requests/receipts. Classification describes observed artifact differences and
supported implementation categories; it does not prove execution equivalence.

## Population, draw and provenance

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

## Classification

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

## What the categories mean for next work

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

## Implications and limits

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

## Every sampled case

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

## Reproduce and verify

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
