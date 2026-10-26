# Arbitrary-length forward Stock scalar CFG production

Validated implementation: `1620b2c4beeb2bc36ee50e79fb40b3b3eb2f320d`, based on #633 (`ac302a8a`).
The default compiler, checker, verified linker and generated-proof consumers now
use proved Stock lowering for scalar jump/return graphs of arbitrary length
whose jumps advance the original source block index. Entry must jump. Bodies
may trap; arguments may be empty; source values may be inherited directly.
Full original #140 remains open.

## Proof and production boundary

Actual source-ranked DFS/RPO/node order derives label order, including synthetic
nodes and shared joins. Retained scan identity, uniqueness and demand transport
connect source successors through arbitrary intervening traversal segments.
Return and first-trap simulation compose from instruction zero through ABI entry
and any number of blocks, deriving the unchanged Scalar.Domain and ABIReadCfg.
Only demanded, available values must be held; omitted or sunk values do not
become materialization requirements. No input proof certificate is introduced.

All production consumers append artifact route 8 while retaining routes 0–7 and
transactional fallback to the complete previous LinearCfg/earlier pipeline on
the original input, allocator and settings. All 2,474 prior backend proof files
and the three existing CompiledSemanticNI theorem headers are exact. There are
no allocator, shared LowerSim or CLIF semantic changes. Old theorem variants,
accepted identities, successful stages and required axiom sets are preserved.

Complete four-block source/ABI witnesses return rotate(7,1)=14 and trap at the
first middle-block zero divisor. Of the 48 added audit roots, 38 generic results
and four kernel witnesses use only the standard three axioms; six fixed-input
witness roots use explicitly labelled original-input checks. MCP reviews confirm
check_sound uses Std3, the complete witness retains exactly its two fixed-input
facts, and neither review reports warnings.

## Terminal author validation

| Gate | Result |
| --- | --- |
| Normal FV/FVTest module keys | 4,093/4,093; 76 rebuilt |
| All trust audits | 94 files; 3,592 roots; all 3,544 prior sets exact |
| Retained ownership checks | 6/6 |
| New integration | 78 checks; 18 generated roots and 4 CLI reconstruction roots |
| Retained linear/scalar-entry/entry/CFG cohorts | 78/70/34/34 |
| Native execution | 24 objects; 24,000 byte executions; 3,000 Cranelift references; zero failures/disagreements |
| Runtime | 5,755 runnable passes; zero failures/disagreements; seven prior unavailable cases |
| Encoder | 1,398 identical; zero different |
| Both E2E modes | 1,159 accepted; all original 1,150 and parent 1,159 identities/stages exact |
| Verified examples | fv-demo: 21 tests/2 ELFs; survey: 53 tests/18 ELFs |
| Actual crate proof package | 93 modules; 96 recorded commands; default build passes |
| Paired default allocator | 4,543 symbols; 900→900 exact; zero gains/losses; four changed instances |

The new maintained native/CLI/link/generated cohort covers 100 source functions
over four to eight blocks, all six ABI configurations, both allocators and both
cleanup modes, including forced complete fallback and missing-oracle controls.
After ordinary Cargo examples rebuilt, all 4,543 actual candidate and reference
function bytes and relocations, source inputs and comparison rows were bound to
the immutable paired capture. No pending gate is counted as passed.

## Register agreement and limits

After the actual CLI i128 legalization, 273 captured instances pass the class,
source, lower and read-boundary checks, and the lowering provider returns actual
Stock output. Ten are newly eligible, all two-block; the prior 263 raw VCode
outputs are exact. This describes the lowering provider, not a claim that every
downstream attempt avoids late fallback. Four- to eight-block activation is
covered by universal proofs and maintained native fixtures; this real capture
contains no eligible instance longer than three blocks.

The four changed byte instances are legalized i128 wrapping add/sub. Stock
removes a duplicate cmp/cset pair (12→10 instructions including prologue;
Cranelift uses 6), leaving carry instruction-selection differences. The same ten
newly eligible cases with the existing regalloc2 option have 0→0 exact matches.
Default allocation is unchanged. These are captured instances and bounded
diagnostics, not unique-function coverage or a full-goal completion percentage.

## Recovery and remaining work

[Machine receipt](stock-forward-cfg-production.json) binds gates to the validated
head. Remote evidence is preserved on
[`95a286c086b9fd3f17215e6a171ece0bd0313867`](https://github.com/eth-act/clifv/tree/95a286c086b9fd3f17215e6a171ece0bd0313867/evidence),
branch agent/stock-cfg-body-progress-20261025T025359Z. The manifest
`evidence/forward-cfg-terminal-manifest.json` lists bounded archive parts and
member hashes. Concatenate parts in numeric order and verify archive SHA256
`0e65715b1b9f970b4630d346155740f327327bd6f8f6465364d7b8f8ac85e0ad` before extraction. Prior archives remain preserved.
No new worktrees, caches or agents were created. Dirty saved work is preserved;
obsolete unlinked cache outputs were cleaned with inode/link/age checks.

Continue correct-choice semantics for ordinary conditional, bit-test and table
branches, actual critical routes, loops with inherited carried values, memory/
addressing/atomics, calls/exceptions and every uncovered reachable rule family.
Reuse existing per-edge prepare/spill/copy proofs. Then close original-domain
whole-driver simulation, Stock-only and downstream completeness. Fallback
preserves acceptance and does not prove completeness.

Saved next work derives actual brif condition/builder/emitter calls and original
condition provenance, plus a semantic boolean-companion-to-branch replacement
with real witnesses, all Std3. These are not whole-branch source simulation yet.
The same-input planning inventory finds 1,695 brif instances but only four with
current scalar bodies, original checks and source-forward control. Thus memory
and calls remain important coverage obligations after control composition.
