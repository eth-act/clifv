# Recovery and continuation plan: test-binary-alignment

Checkpoint: 2026-10-13. Task: [#140](https://github.com/eth-act/clifv/issues/140).
The full objective remains **unfinished**: prove the preserved Stock lowering
driver and switch production while retaining accepted-input and theorem parity.
This file is the resume entry point; the smaller family plans are supporting records.

Latest validated local batch: scalar rotations,64 complete source/record witnesses,
482 audited roots (428 prior +54 new). See the
[rotation receipt](../research/stock-rotate-audit.json) and final checkpoint below.
Whole-driver simulation/completeness, uncovered families/effects and production
integration remain required; production still uses the legacy driver.
The initial recovery snapshot and earlier checkpoints are retained as history.

## Resume location and preservation

- Work in `/home/lee/clifv/.worktrees/driver-proof-resume`, branch
  `agent/stock-logic-not-values-pr`. Initial recovery base was
  `cc29aaa494ddea10a8e38b5dd5fad707dcee47b6`; current local tip is recorded in #44.
  GitHub main was independently checked at the same commit during recovery.
- `/home/lee/clifv` is the historical `test-push` checkout at `f866008`, with dirty
  October 5 diagnostic evidence. Its `main` branch and proof roadmap are stale.
  Do not reset it or copy its old compiler sources over the active worktree.
- At initial recovery, seven local `StockLogicalNot*.lean` files and the family plan were
  untracked, uncommitted and unpublished. Subsequent local validated batches are
  recorded below; preserve those sources and the original backup.
- All 38 dirty primary-checkout files and all eight dirty active-worktree files
  were copied and SHA256 verified in
  `/home/lee/.clifv-recovery/20261013T110839Z/manifest.json`. Binary diffs accompany
  the snapshots. This backup precedes the recovery documentation additions.
  Restore individual files only after comparing the manifest and current contents.
- The interrupted session remains at
  `/home/lee/.codex/sessions/2026/10/05/rollout-2026-10-05T23-54-09-01a10f58-ef03-7df3-9d8c-c8c0e16be9be.jsonl`.
  Its last substantive updates confirm the mirrored-root/source connection; the
  final user request asks for a plan file. The disconnect does not identify a
  compiler failure or explain the account's credit display.

## Progress and evidence

| Work | State | Evidence / limitation |
| --- | --- | --- |
| Legacy dead-instruction cleanup #137 | Landed | Historical receipt/status reports default exact matches 465 → 671; original driver retained. |
| Register alignment wrapper #139 | Landed, opt-in | Status reports 671 → 959 (+288, no losses) with focused gates; wrapper alone does not complete #140 or change the production baseline below. |
| Stock alias/domain/termination, availability and fresh-write groundwork | Landed proof slices | Existing Stock modules and plans; these are prerequisites, not whole-driver correctness. |
| Logical helper/root/record/source proofs #177–178 | Landed | Commits `de405b6`, `cd324c7`; reused by current work. |
| Scalar NOT and fused LSL/NOT #179 | Landed and validated | `cc29aaa`; GitHub confirms merged PR, all three CI checks successful. |
| Fused binary logical-NOT batch | Fully validated locally | `a739ad5`; complete NOT-of-XOR/retained/source witnesses and full gates recorded in `stock-logical-not-values-audit.json`. |
| Subsequent scalar proof families | Fully validated locally | Multiplication, shifts, casts/reduction, source-scope partition, negation, bit reversal/byte swap, unary dispatch and counts; receipts and commits below. |
| Scalar rotations | Full family batch validated locally; commit pending | All12 selected roots/retained/source/dispatch,64 complete witnesses,54 new standard-only roots and all full gates; `stock-rotate-audit.json`. |
| Production Stock-driver cutover | Pending | No whole-driver simulation/completeness or actual production switch demonstrated. |

The committed [#179 audit](../research/stock-bnot-values-audit.json) records full
build 1471 jobs, crate proofs 1171 jobs, runtime 4672 passes/0 failures/0 errors/0
disagreements with seven unchanged not-runnable cases, encoder 1292 identical/0
different, and E2E 1150 accepted/0 rejected with identity/stage parity against
#178. Its nine source hashes, six gate-log hashes and identity-report hash were
independently checked during recovery. These results cover the landed batch;
they described only the landed batch at initial recovery. Subsequent local full
gates are recorded in their dated receipts below.

The [#179 CI comparison](https://github.com/eth-act/clifv/pull/179) reports
671 exact function outputs, 939 different, 432 setting rejections and 2413
unsupported-operation rejections from 4455 outputs. All 1302 official files
were inventoried; 151/484 AArch64 files had outputs compared. The change was
+0/−0 exact outputs. Full metadata agreement remains unestablished, and the
comparison job did not execute compiled functions. Proof progress has not yet
increased default byte agreement.

## Current local module map

All paths below are under `FV/Backend/Proof/` in the active worktree.

| File | What exists now |
| --- | --- |
| `StockLogicalNotReceipts.lean` | Five thin RHS/match contracts reuse landed identical helper expressions. |
| `StockLogicalNotSemantics.lean` | Register, immediate and LSL NOT machine values through final aliases, with fresh-write preservation. |
| `StockLogicalNotValues.lean` | Actual successful term-566 helper value composition, with demanded-value guards. |
| `StockLogicalNotWitness.lean` | All nine operation/helper-form executions; fused source values need not be materialized in machine registers. These are helper witnesses. |
| `StockLogicalNotLookthrough.lean` | Actual nested NOT pattern yields original source definition and complement value. |
| `StockLogicalNotRootValues.lean` | Typed RHS/output wrapper composition for the six mirrored binary roots. |
| `StockLogicalNotMatch.lean` | Successful matching derives canonical environment and hidden NOT source; `stock_not_selected_root_values` proves original binary values for all six mirrored roots. |

Fresh recovery verification: memory-capped normal build of `StockLogicalNotMatch`
and `StockLogicalNotWitness` completed successfully (368 jobs), covering all
seven modules. A normal Lean `#print axioms` audit checked all 17 public roots.
No full repository gates or new Lean MCP checks were run during recovery.
See [recovery receipt](../research/test-binary-alignment-recovery.json) for
source/log hashes. Existing family-plan claims of earlier MCP checks remain
historical evidence, separate from this fresh verification.

## Next bounded batch

1. **Start from the compiled selected-root theorem.** Read `StockLogicalNotMatch`
   and the landed `StockLogicalRecordValues` / `StockBnotRecordValues` templates.
   Do not redo the canonical-match or term-566 helper proofs.
2. **Finish the seventh fusion, `bnot(bxor)`.** Identify its actual selected rule,
   match/RHS execution and original-source value. It is not included in the six
   mirrored `notRule` cases. Reuse existing scalar NOT and XOR helper semantics.
3. **Connect actual retained records and result binding.** Reuse existing
   whole-run record origins, final resolver and allocation bounds; derive
   selection and binding internally. Preserve the original restricted-frame
   DFG, demand/availability guards and source scope. Do not introduce a caller
   match certificate or silently treat demanded later definitions as available.
4. **Compose guarded original-source transfer.** Establish value preservation
   through final aliases and fresh writes. Follow the landed record/source proof
   structure; do not infer execution value equality from alias provenance alone.
5. **Supply complete non-vacuity witnesses.** Cover the six mirrored roots and
   seventh fusion at 32/64 bits, actual retained records and source steps,
   nonempty binding, and fused constants/shifts absent from machine registers.
   Existing helper witnesses alone do not discharge these obligations.
6. **Validate one reviewable batch.** Check every new public root with Lean MCP
   and normal kernel/transitive axiom audits, preserving all 226 prior audited
   roots and final compiler axiom sets. Run full gates below and capture a compact
   incremental receipt. Update the family plan and #44 with exact evidence.

## Gates and shell setup

The recovery shell initially lacked `lake` on PATH; supplying the pinned
toolchain fixed the invocation. Use the active worktree and memory cap:

```sh
cd /home/lee/clifv/.worktrees/driver-proof-resume
export PATH=/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:/home/lee/.cargo/bin:$PATH
export LEAN_NUM_THREADS=2 FV_MEMCAP=22G
scripts/memcap.sh lake build FV.Backend.Proof.StockLogicalNotMatch FV.Backend.Proof.StockLogicalNotWitness
```

Before calling the completed batch merge-ready, run `lake build FV FVTest
lean-backend lean-e2e-check link-check`, crate-proofs `lake build`, all relevant
public-root/E2E axiom audits, `scripts/lean-backend-filetests.sh`,
`scripts/lean-backend-encode-check.sh`, and both relevant E2E modes with full
identity/stage parity. Wrap every lake/cargo invocation in `scripts/memcap.sh`.
Preserve at least the actual #179 baseline above, not just older roadmap minima.
If CLIF semantics change, add CLIF filetests and optimizer differential gates.
Require a fresh complete stock comparison before behavior/default changes.
The landed audit and `/tmp/stock-bnot-gates.sh` document existing tool paths;
capture fresh logs rather than overwriting historical receipts.

## Remaining full-goal obligations

After this batch, inventory the uncovered selected rule families and effectful
cases. Prove execution semantics for memory, calls, traps, control flow and
omitted/sunk instructions with a sound deferred-effect invariant. Compose
source/block/whole-driver simulation and completeness under the original input
conditions, then integrate the actual driver into compiler, checker, linker and
generated-proof consumers. Preserve old theorem variants, accepted identities
and successful stages; validate runtime, encoder and complete stock comparison.
Only this completed production cutover can satisfy #140. Do not estimate a
completion percentage from the number of proof slices or merged PRs.

## Coordination and stopping rules

Read current #44/#52/#71 and #140 before further implementation; stale entries
are uncertain. #140 remains the existing claim. Kev owns #42/T6; this recovery
changes no IselLcf/Cov/optimizer interface or fixed-proof migration. Flag concrete
overlaps and pause only the conflicting portion. Preserve archived driver WIP
and historical dirty reports; reuse their implementation when relevant.

Primary-checkout AGENTS/worktree rules supplied by the user take precedence over
the active checkout's stale `/home/kev/work/clifv-wt` instruction. New linked
worktrees belong under `/home/lee/clifv/.worktrees` and use the primary helper.
Repository §7 prohibits agent push, merge, rebase, stash and pattern-kill actions;
this recovery authorizes none. Any later user-authorized merge must be squash.
No commit, push, merge, process termination or compiler-source edit was performed
for recovery. Update #44 after a commit, scope change or stop.

At each stop, record HEAD, exact dirty paths/hashes, successful and outstanding
checks, next theorem and local-only/publication state in this plan or its receipt.
After another disconnect, read this file and compare the saved receipt with
current sources before continuing. Keep #140 incomplete while any full-goal
obligation remains.

## Active continuation checkpoint

Updated UTC: 2026-10-13T11:34:51.875968+00:00

- User resumed the full #140 goal; live #44/#52/#71 and #140 read, #44 updated active. No concrete shared-interface conflict; T6 boundary retained.
- Added `StockLogicalNotXor.lean`: actual rule1406 match derives hidden XOR source operands, canonical typed environment, unchanged scheduling state and original NOT-of-XOR execution value. Normal target build380jobs passes; selected root MCP audit standard3/no source warnings.
- Added `StockLogicalNotRecord.lean` and `StockLogicalNotXorRecord.lean`: actual retained-record selection/binding/code and guarded demand/availability value transfer. Both normal target builds pass; both guarded public roots pass MCP standard3/no source warnings.
- Added `StockLogicalNotXorWitness.lean`: complete actual register-form record/source witnesses at32/64; normal target build passes.
- `StockLogicalNotRecordWitness.lean` (six mirrored roots32/64) and `StockLogicalNotXorFusedWitness.lean` (unmaterialized constant/shift32/64) are under normal kernel build; do not count them complete until fresh success.
- Current processes/logs: witness build session67553 `/tmp/driver-resume_witness2-build.log`; fused witness session32248 `/tmp/driver-resume_fused-witness-build.log`. Prior XOR failures were corrected; preserve earlier logs as development evidence.
- Full batch gates, all-root MCP/kernel/transitive audit, compact receipt and complete identity/stage parity remain. All new files local/untracked/uncommitted/unpublished. HEAD remainscc29aaa; no push/merge, no runtime/compiler changes.
- Then inventory remaining rule families/effects and continue source/block/whole-driver simulation/completeness and production consumers. Goal remains active and incomplete.

## Fused-NOT batch validated

The next bounded batch above is complete locally: seventh NOT-of-XOR; all seven
retained-record/binding/source transfers; complete32/64 witnesses, including
unmaterialized constants/shifts; all full gates and public-root audits. Evidence:
[stock-logical-not-values-audit.json](../research/stock-logical-not-values-audit.json).
Full1484/crates1171/runtime4672/0fail/0disagree/7known non-runnable; encoder1292/0;
bothE2E1150/0 and exact #179/between-mode identity-stage parity. All256 normal
roots checked:226 prior trust sets unchanged,30 new roots standard-only; all30
fresh MCP roots pass. Thirteen fused-NOT modules saved; no production behavior
changed. Witness build sessions67553/21708 and full gates70706 completed.

Next: [remaining-family plan](stock-driver-remaining-families.md), backed by the
[517-root source inventory](../research/stock-driver-rule-inventory.json).
Fifteen identified guarded record bridges are evidence of local semantics, not
whole-driver completion. Classify the other roots against original LowerScope,
then prove selected execution, effects/control/omission/sinking and compose
whole-driver simulation/completeness before production consumers/cutover.
The full goal remains active and incomplete. No push or merge.

## Multiplication continuation checkpoint

Updated UTC: 2026-10-13T12:08:16.964109+00:00

The prior goal turn made verified progress: local commit a739ad5 and all256
root audits/full gates pass; goal remains active. Current base is a739ad5.
New work: actual base multiply plus three multiply-add/subtract roots, retained
records/binding and original guarded source transfer. Normal targets pass;
base32/64 full witnesses pass; fused32/64 unmaterialized-product witnesses
building in session60091. Both guarded roots MCP standard3/no warnings.
All12 modules are local/untracked/uncommitted. No runtime/compiler changes.
Resume from [stock-multiply-values.md](stock-multiply-values.md), finish witnesses,
all25 new/all256 prior audits and full gates, then continue original full goal.
No push or merge; primary/archived work preserved.

## Multiplication batch validated

Updated UTC: 2026-10-13T12:15:35.676394+00:00

Base multiply and allthree MADD/MSUB fused roots now have actual request/state,
match/source/selection, machine/final-alias, retained-record/binding and guarded
source-transfer proofs, with complete32/64 full witnesses and unmaterialized
product. All12 modules pass;25 new MCP/normal standard-only roots; all256 prior
trust sets and final compiler sets unchanged. Full1496/crates1171/runtime4672/0fail/
0disagree/7known non-runnable; encoder1292/0; bothE2E1150/0 with exact prior/#179
and between-mode identity-stage parity. Evidence:
[stock-multiply-values-audit.json](../research/stock-multiply-values-audit.json).
Witness session21610 and gates77649 completed; no compiler/runtime change.

Next: scalar shifts (all four do_shift selections and original narrow-type
extensions), then remaining families/effects and full source/block/driver
simulation/completeness/cutover. Inventory identifies19 guarded record bridges
among517 generated lower roots; this is not whole-driver coverage. Goal active
and incomplete. No push or merge; preserve current local proof stack.

## Scalar shift/extension foundation checkpoint (2026-10-13)

Ten new local modules build. All four actual extension helpers derive guarded
mapped requests and original extension/pass-through values. Immediate, register
and masked-register shift RHSs have complete state contracts, inverse guarded
request receipts and actual executions; all three final-alias machine contracts
have complete witnesses with dirty upper bits. The mask RHS uses the real
six-slot environment, with both local slots initially empty. Its interpreter
composition is proved over an abstract semantics and then instantiated with
Stock, avoiding an expensive kernel reduction without weakening the statement.

Fresh validation: 1506 full build jobs; 1171 crate jobs; 4672 runtime passes, 0
failures/disagreements and 7 unchanged non-runnable cases; 1292 encoder matches, 0
differences; 1150 accepted/0 rejected in each E2E mode. Complete accepted identity
and stage lists equal the multiply checkpoint and each other. All26 new public
roots passed normal and MCP/kernel checks with only standard axioms; all 281 prior
sets are unchanged (307 roots total). See the
[foundation audit](../research/stock-scalar-shift-foundations-audit.json) and
[family continuation](stock-scalar-shift-values.md).

This foundation checkpoint adds no driver root to the 19 recorded bridges. Next:
compose all actual do_shift selections; connect all six shift source roots,
retained-record binding and guarded original-source transfer; derive scratch
separation from existing record availability; add full source/record witnesses.
Then continue all uncovered families/effects, source/block/whole-driver
simulation and completeness, and production integration/stock comparison.
The original scope, old variants, successful stages, trust sets and saved work
remain preserved. Production is legacy; #140 remains unfinished. No push or merge.


## Scalar-shift source witnesses and normal gates complete

Updated UTC: 2026-10-13T23:10:09.019988+00:00

The witness receipt/source proof split builds383jobs. Complete24-case actual retained-record/source witnesses cover all scalar widths, three operations and literal/register counts; literal counts stay unmaterialized. Full1515/crates1171/runtime4672 with0fail/0disagree and7unchanged known non-runnable; encoder1292 identical/0different; bothE2E1150accepted/0rejected, all full identities/stages match each other and the previous foundation batch. Normal323-root audit preserves all307 prior sets and gives16 new standard-only roots.

Final MCP witness checks/source scan are pending; source-copy MCP verification is re-elaborating expensive concrete receipts, and a compact imported-root audit is prepared. Do not call this completed batch merge-ready or update inventory until those checks finish. See docs/research/stock-scalar-shift-record-checkpoint.json. Full #140 remains active and incomplete; production legacy, no push/merge. The next extension draft at /tmp/driver-resume_cast-receipts.lean kernel-checks actual base zero/sign-extension matches, requests, emissions and all six widening semantics; selected-root draft checks locally. No complete extension record/source witnesses or full family coverage claimed.


## Scalar-shift family validated locally

Updated UTC: 2026-10-13T23:14:39.055969+00:00

All four actual count selections, six scalar shift roots, retained-record/result binding and original guarded source transfer are complete locally, with24 complete source/record witnesses including unmaterialized literal counts. Scratch/input separation is derived from original availability; the prior full-demand helper variant is retained. Nine new modules build. All16 new public roots pass MCP and normal standard-only audits; all307 previous sets are unchanged (323 total). Original sources have0 MCP source-warning patterns. The expensive computational witness receipts are separated from the source witness, and MCP audits import compiled declarations to avoid redundant source elaboration.

Full1515/crates1171/runtime4672 with0fail/0disagree and7unchanged known non-runnable; encoder1292 identical/0different; bothE2E1150accepted/0rejected with exact full identity/stage parity. Durable receipt: docs/research/stock-scalar-shift-record-audit.json. Source inventory now identifies25 guarded record bridges among517 generated source roots; this is not whole-driver coverage or a completion percentage.

Full #140 remains active and incomplete. Production remains legacy. Continue extension/reduction roots, remaining families/effects/control, source/block/whole-driver simulation and completeness, and actual compiler/checker/linker/generated-proof production integration. Require fresh complete stock comparison before cutover. No push or merge.


## Base zero/sign-extension batch validated locally

Updated UTC: 2026-10-13T23:46:20.013931+00:00

Five modules,11 new standard-only normal/MCP roots, all323 prior sets unchanged (334 total). Actual base roots1261/1315, all six widening pairs, retained binding/original source-step transfer and12 complete dirty-upper-bit source/record witnesses; missing-type rejection has an actual context-build witness. Original successful source evaluation supplies the widening condition internally. Full1520/crates1171/runtime4672 with0fail/0disagree and7known non-runnable; encoder1292/0; bothE2E1150/0 with complete identity/stage parity. Receipt docs/research/stock-scalar-cast-audit.json; continuation docs/plans/stock-scalar-casts.md. Source inventory now identifies27 guarded bridges, not whole-driver coverage. Next reduction aliases using existing final-edge/endpoint proofs, then all remaining full-goal obligations. Production legacy; full #140 active/incomplete, no push/merge.


## Reduction batch validated locally

Updated UTC: 2026-10-14T00:13:27.240682+00:00

Five modules prove actual reduction root2146, its complete no-allocation/no-emission state, retained alias binding and final source/result endpoint equality, and original successful narrowing source-step transfer. Existing whole-driver alias edge/endpoint proofs are reused. Twelve complete source/record witnesses cover all six narrowing pairs, both parameter sources and earlier constant producers; the latter deliberately leaves the original source vreg unmaterialized. Machine registers/source memory are unchanged by the actual empty record. No fresh-result or additional accepted-input certificate is assumed.

All8 new public roots pass normal/MCP standard-only audits and original-source scans with0 warnings; all334 earlier sets are unchanged (342 total). Full1525/crates1171/runtime4672 with0fail/0disagree and7unchanged known non-runnable; encoder1292 identical/0different; bothE2E1150accepted/0rejected, every identity/stage equal to previous and each other. Receipt docs/research/stock-reduce-audit.json.28 identified guarded bridges among517 generated roots is an inventory, not whole-driver coverage. Static opcode/type-pattern family classification saved in docs/research/stock-driver-rule-families.json; it does not prove reachability/exclusion.

Full #140 remains active and incomplete. Next: scope-derived exclusions for unsupported opcode/type patterns, remaining arithmetic/logical/count/rotation/reversal, comparisons/selects and extension/look-through families; memory/call/control/trap and deferred-effect semantics; source/block/whole-driver simulation/completeness; actual compiler/checker/linker/generated-proof production integration and fresh complete stock comparison. Production legacy; no push or merge.


## Ordinary-source root exclusions validated locally

Updated UTC: 2026-10-14T00:25:34.544757+00:00

Original mapped source scope proves372 of517 generated lower roots cannot match ordinary source instructions. Actual first-match and retained-record selection derives membership in the145 remaining closure roots internally. Exact partition counts are kernel-checked; concrete excluded-root and complete emitted-source witnesses pass. This is scope exclusion, not execution coverage; terminator/branch contexts remain separate.

All10 new roots normal/MCP standard-only;342 prior sets unchanged (352 total),0 source warnings. Full1528/crates1171/runtime4672 with0fail/0disagree and7known non-runnable; encoder1292/0; bothE2E1150/0 with full identity/stage parity. Receipt docs/research/stock-source-scope-audit.json; plan docs/plans/stock-source-scope.md. Inventory/family classification now links proof-backed ordinary-source exclusions. No legacy Cov/T6/IselLcf/optimizer interface or production changes. Next remaining closure execution/source transfer, effects/control/deferred semantics, full simulation/completeness and actual production integration/complete stock comparison. Full #140 active/incomplete; no push/merge.


## Scalar negation continuation

Updated UTC: 2026-10-14T00:43:19.040804+00:00

Five StockNeg core modules build and the full source witness tail checks.
The eight-case concrete witness build is live; audits and full gates are
prepared. See stock-scalar-negation.md. Previous goal turn made concrete
progress by assembling and launching the full witness module; it was not
blocked. Full #140 remains active/incomplete, production legacy, no push/merge.


## Scalar negation validated locally

Updated UTC: 2026-10-14T00:47:24.136622+00:00

Six modules prove actual scalar negation root857/id756, full state/trace,
resolved subtraction from zero, real retained result binding and original
source transfer with existing demand/availability guards. Eight complete
source/record witnesses cover all four scalar widths, parameter operands and
earlier constant producers with original source registers unmaterialized and
dirty upper bits. All8 new roots normal/MCP standard-only;352 prior sets
unchanged (360total);0 original-source warnings. Full1534/crates1171,
runtime4672/0fail/0disagree/7known with identical report, encoder1292/0;
bothE2E1150/0 with complete identity/stage parity. Receipt stock-neg-audit.json.

29 guarded bridges among517 generated roots remains an inventory, not whole-
driver execution coverage. Next remaining closure arithmetic/count/rotation/
reversal/comparison/select/extension/look-through families; effects/control and
deferred invariants; full source/block/whole-driver simulation/completeness;
actual production integration and fresh complete stock comparison. Full #140
active/incomplete; production legacy; no push or merge.


## Bit-reversal core saved, family unfinished

Updated UTC: 2026-10-14T00:55:34.220179+00:00

Local/unpublished HEAD 1fd7e7dca84a40136b7ff3bcbb5c672eca57c101. Three untracked modules StockBitHelper,
StockBitrevRhs and StockBitrevSemantics build. Six new core roots normal/MCP
standard-only;0 original-source warning patterns. Shared BitRR helper retains
full scheduling state; all three bit-reversal root matches/RHSs are proved.
A generic kernel bit-index proof covers narrow reversal followed by shift,
including dirty upper bits. Exact source hashes and pending steps are saved
in docs/research/stock-bitrev-core-checkpoint.json. No full bit-reversal witness
or record/source composition or new full gates claimed. Last complete batch
remains stock-neg-audit.json (360 audited roots). Next derive guarded RHS
requests and fallback width restrictions, then resolved execution/selected
values, retained binding/original source transfer and eight complete witnesses.
Full #140 active/incomplete, production legacy; no push or merge.


## Scalar bit reversal validated locally

Updated UTC: 2026-10-14T01:12:20.511148+00:00

Eight modules cover actual roots1931/1937/1946 (ids915/916/918), complete
matching/RHS scheduling state, success-derived operand requests, first-match
wide fallback constraints, resolved scalar values, actual retained result
binding and original guarded source transfer. Kernel bit-index reasoning proves
narrow reversal/shift correctness independently of dirty upper bits. Eight
complete source/record witnesses expose actual selected roots, emitted decisions
and nonempty bindings at8/16/32/64, including parameter and unmaterialized earlier
producer operands. The previous partial core checkpoint is historical evidence;
current complete source hashes and gates are in stock-bitrev-audit.json.

All14 new roots normal/MCP standard-only;360 prior sets unchanged (374total),
0 source warnings. Full1542/crates1171/runtime4672/0fail/0disagree/7known with
identical report; encoder1292/0; bothE2E1150/0 with complete identity/stage parity.
32 identified guarded record bridges among517 roots remains an inventory, not
whole-driver coverage. Remaining count/byte-swap/rotation, arithmetic/comparison/
select/extension/look-through families, effects/control/deferred invariants,
full source/block/whole-driver simulation/completeness and actual production
integration/complete stock comparison remain required. Full #140 active and
incomplete; production legacy; no push or merge.


## Byte-swap math saved, family unfinished

Updated UTC: 2026-10-14T01:17:54.573264+00:00

Local/unpublished HEAD 0004573d291c0d7b8d17d73d65c56aba7773e43c. StockBswapSemantics builds362jobs.
Two new math roots pass normal/MCP standard-only audits,0 source warnings.
Halfword REV16 low-bit correctness uses kernel bit-index reasoning rather
than legacy bit-blasting; generic word/doubleword contracts use exact operand
width. Source hashes and pending work: stock-bswap-core-checkpoint.json.
Next actual roots2035/2038/2041 match/RHS/request contracts, resolved execution
and selected values, retained binding/original source transfer, six complete
16/32/64 parameter/earlier-producer source witnesses, full prior-root/gate
validation. Last complete batch: stock-bitrev-audit.json (374roots).
Full #140 active/incomplete; production legacy; no push or merge.


## Byte swaps and source-driven unary transfer validated locally

Updated UTC: 2026-10-14T01:42:03.876677+00:00

Seven modules cover actual roots2035/2038/2041 (ids932/933/934), full match/RHS
state, success-derived mapped requests, resolved values, retained binding and
original source transfer. Kernel bit-index reasoning proves REV16 correctness
without legacy byte-swap bit-blasting. Six complete16/32/64 source/record
witnesses expose real selected roots/nonempty bindings, parameters and earlier
producers with original source registers unmaterialized. Halfword fixtures
include dirty bits just above16 bits inside the physical32-bit operand.

StockUnarySourceValues derives restricted typed operands from actual original
source success and unchanged dominance. Getter-free negation/bit-reversal/
byte-swap variants preserve earlier theorem variants; new byte-swap fixtures
use the source-driven interface. The older8+8 complete negation/bit-reversal
fixtures still inhabit their unchanged source/input conditions. Initial witness
build370jobs and source-driven build403jobs pass. All14 new roots normal/MCP
standard-only;374 previous sets unchanged (388total),0 source warnings.
Full1549/crates1171/runtime4672/0fail/0disagree/7known with identical report;
encoder1292/0; bothE2E1150/0 with complete identity/stage parity. Current source
hashes/gates: stock-bswap-audit.json; the previous math checkpoint is historical.

35 guarded bridges among517 generated roots remains an inventory, not whole-
driver coverage. Next derive actual selected-rule families from original source
opcode/type data, then remaining families/effects, deferred invariants, full
source/block/whole-driver simulation/completeness, actual production integration
and fresh complete stock comparison. Full #140 active/incomplete, production
legacy; no push or merge.


## Opcode-based dispatch inventory saved, matching connection pending

Updated UTC: 2026-10-14T01:48:35.817774+00:00

Local/unpublished HEAD b0c23c47dee59996ce0f1e4448599dffa5213e2b. StockRootOpcode builds352jobs.
Three new inventory roots normal/MCP standard-only,0 source warnings. Kernel
checks every original closure root has a recognized primary opcode; negation
candidates exactly[756], byte swaps[932,933,934]. This is syntax coverage, not
execution or matching correctness. Current hashes/pending work are saved in
stock-root-opcode-checkpoint.json. Next prove sourceOpcodePattern matching
soundness via canonical inst_data_value/enum inversions, handle the same bind/and
wrappers as legacy rootFmt, transport to actual Stock LowerSelection and derive
selected families from original source data/closure membership. Then remove
unary source-transfer rule-id premises and provide complete actual witnesses/
full gates preserving388 prior sets. Last complete batch stock-bswap-audit.json.
All remaining full #140 obligations persist; production legacy; no push/merge.


## Actual opcode dispatch and unary source variants validated locally

Updated UTC: 2026-10-14T02:18:14.895065+00:00

Six modules prove primary-opcode recognition for all145 closure roots, its
sound actual pattern/matching/retained-record connection, and exact negation,
bit-reversal and byte-swap selection from original opcode/type data. Wide
bit-reversal constraints reuse actual rejected-prefix selection. New source-
by-instruction variants derive operand getter and selected rule id internally;
old theorem variants and original input conditions are unchanged.22 complete
source/record witnesses (negation8,bit reversal8,byte swaps6) use the new interface,
with actual emitted decisions/root ids/nonempty bindings, final-alias execution,
original post-frames, parameter/unmaterialized-producer forms and dirty upper bits.
All three witness targets407jobs pass. All16 new roots normal/MCP standard-only;
388 prior sets unchanged (404total),0 source warnings. Full1555/crates1171/
runtime4672/0fail/0disagree/7known identical report; encoder1292/0; bothE2E1150/0
with full identity/stage parity. Receipt stock-unary-dispatch-audit.json;
plan stock-unary-dispatch.md. Earlier opcode checkpoint is historical.

The complete diagnostic primary-opcode family lists (60groups/145roots) are
saved in stock-root-opcode-families.json. Source matching is now connected to
these candidates; remaining families still need execution/source-transfer proofs.
35 guarded bridges remains an inventory, not whole-driver coverage. Next other
covered-family source-based dispatch and remaining count/rotation/arithmetic/
comparison/select/extension/look-through, effects/control/deferred invariants,
full source/block/whole-driver simulation/completeness, production integration
and fresh complete stock comparison. Full #140 active/incomplete; production
legacy; no push or merge.


## CLZ/CTZ core saved, family unfinished

Updated UTC: 2026-10-14T02:50:25.819263+00:00

Local/unpublished HEAD 9bab3587f95c05902d25209d235dacf9bae50399. Three local uncommitted modules
StockCountMath/StockImm12Helper/StockCountRhs build371jobs. All7 core roots
normal/MCP standard-only,0 source warnings. Kernel widening/correction and
reverse/sentinel math covers zero inputs/dirty upper bits. All six actual
count matches and complete RHS states cover8/16/32/64, including narrow CLZ
extension+count+subtraction and CTZ reversal+sentinel+count. No selected/
retained/source transfer or complete family witnesses/gates claimed yet.
Current hashes/pending steps: stock-count-core-checkpoint.json; plan
stock-scalar-counts.md. Next success-derived requests, resolved values/fresh
intervals, original DFG-derived CLZ input type, actual selection, retained
binding/source transfer and complete zero/nonzero source witnesses; preserve
all404 prior trust sets/full gates. Last full batch stock-unary-dispatch-audit.json.
Full #140 active/incomplete; production legacy; no push or merge.


## CLZ/CTZ retained/source and actual dispatch checkpoint

Updated UTC: 2026-10-14T03:13:57.189868+00:00

Eight local uncommitted modules now build through StockCountSourceValues (413
jobs). The failing wide request inversion is fixed by reducing canonical
environment conditions. Successful narrow CLZ derives an actual context type;
original restricted DFG/frame consistency identifies the source width, rather
than adding a caller type certificate. Kernel machine semantics prove CLZ/CTZ
at8/16/32/64 through final aliases and preserve all registers outside the
actual1/2/3-register allocation, including zero counts and dirty upper bits.
Actual successful selection, retained records, result binding and guarded
original source transfer are connected. The source-by-instruction variant
derives its getter and rule internally; opcode/type matching and rejected
narrow prefixes establish both wide fallbacks. Existing variants preserved.

20 public roots have matching normal/MCP standard-only axiom sets;8 current
source scans have0 warnings. Receipt stock-count-values-checkpoint.json;
raw stock-count-dispatch-mcp-verify.json. Earlier core/18-root receipts are
historical. No complete family witness or full batch/gate claim yet. Last full
validated batch remains stock-unary-dispatch-audit.json (404 roots).

Next:32 complete witnesses(twooperations×fourwidths×parameter/earlierproducer×
zero/nonzero), actual source/records/nonempty bindings/post-frames and narrow
CLZ DFG guard; then preserve404 prior roots/seven exact compiler trust sets
and full/crate/runtime/encoder/bothE2E gates. All remaining original family,
effect/control/deferred, source/block/whole-driver simulation/completeness,
production integration and fresh complete Stock comparison obligations remain.
Full #140 active/incomplete; production legacy; no commit/push/merge this batch.


## Scalar CLZ/CTZ batch fully validated locally

Updated UTC: 2026-10-14T03:34:39.341521+00:00

All8/16/32/64 count paths have actual request/type inversion, kernel alias-
resolved machine values and fresh preservation, selected execution, retained
result binding and original guarded source transfer. Opcode/type matching and
rejected narrow prefixes derive selected rules internally; source-by-instruction
transfer derives its getter. Narrow CLZ type follows successful execution plus
original restricted DFG/frame consistency. Earlier theorem variants remain.
32 complete source/record witnesses cover CLZ/CTZ × fourwidths × parameter/
earlierproducer × zero/nonzero, dirty upper bits, actual nonempty bindings,
source steps/post-frames and the inhabited DFG guard. Four targets415jobs pass.

24 new public roots normal/MCP standard-only,404 prior sets unchanged (428total),
all7 final compiler trust sets unchanged;12 source scans0warnings. Full1567/
crates1171/runtime4672/0fail/0disagree/7known report byte-identical to prior;
encoder1292identical/0different;bothE2E1150accepted/0rejected with everyidentity/
stage unchanged. Receipt stock-count-audit.json; compressed complete logs and
identity reports archived with SHA256 in that receipt. Earlier count checkpoints
are historical. Inventory41 guarded record bridges/517 roots is not whole-driver
coverage or a completion percentage. No compiler/default/accepted-input changes.

Next remaining count/rotation/arithmetic/comparison/select/extension/look-through
families and effects/control/deferred invariants, then full original source/
block/whole-driver simulation and completeness, actual compiler/checker/linker/
generated-proof production integration, and fresh complete Stock comparison.
Full #140 active/incomplete; production legacy; no push or merge.


## Scalar rotation core checkpoint; family unfinished

Updated UTC: 2026-10-14T03:54:25.120102+00:00

Local/unpublished HEAD3221a28. Three uncommitted StockRotateMath/Semantics/Rhs
modules build378jobs. All9 roots normal/MCP standard-only;3 source scans0warnings.
Kernel narrow opposite-count identity removes the legacy bit-blasting dependency
without changing old theorem interfaces. Wide register/immediate final-alias
values and narrow register/immediate pure kernels preserve both sides of actual
allocation intervals. Actual helpers513/514 and all eight wide root RHSs have
complete scheduling/base/request states. Source protection remains an internal
proof obligation to derive from original available-source alias bounds, never
a new source condition/certificate or below-frontier alias restriction.

Current hashes/pending obligations:stock-rotate-core-checkpoint.json; plan
stock-scalar-rotations.md. Narrow actual helpers/RHSs, matching/constant values,
selection/requests, retained binding/guarded source transfer, complete family
witnesses and all428-prior/seven-final trust/full gates remain. Last full audit
stock-count-audit.json. All original remaining rule/effect/control/deferred,
full simulation/completeness, actual production integration and fresh complete
Stock comparison obligations persist. Full #140 active/incomplete; production
legacy; no commit/push/merge this partial batch.


## Narrow helper and preparation checkpoint

Updated UTC: 2026-10-14T04:16:10.279651+00:00

Six local/uncommitted rotation modules now build through StockRotateNarrowRoots
(381jobs). StockRotatePure proves constructor closure for34 pure reachable terms
and transports base-state helper execution to Stock while preserving every
scheduling field. StockRotateNarrowRhs proves actual710/712 executions with
complete six/three-instruction fragments. Register execution splits the8/16
cases to avoid excessive kernel recursion from the symbolic-width proof; no
checking bypass or oracle was added. Direct/failed drafts remain saved in /tmp.
StockRotateNarrowRoots supplies actual guarded typed zero-extension preparation.

13 public roots normal/MCP standard-only;6 source scans0warnings; current hashes
and raw audit evidence:stock-rotate-narrow-checkpoint.json. Earlier9-root core
receipt remains historical. Last full validated batch remains stock-count-audit.json
(428 roots). Complete rotation family witnesses/full gates remain pending.

Next compose the four narrow instruction-root RHSs from preparation, exact
intermediate source-request states and actual narrow helpers. Derive the input
type from original restricted DFG/frame consistency in selected-source proofs.
Then original matching/constant look-through, successful-request inversion and
opcode/type/priority selection, retained binding and availability-derived source
protection, guarded source-step transfer, complete12-root witnesses and all428
prior/seven-final audits/full gates. All original remaining families/effects/
control/deferred, full source/block/whole-driver simulation and completeness,
actual production integration and fresh complete Stock comparison remain.
Full #140 active/incomplete; production legacy; no commit/push/merge this batch.


## All rotation RHSs and register matching checkpoint

Updated UTC: 2026-10-14T04:31:27.423666+00:00

Seven local/uncommitted modules build through StockRotateMatch (382jobs). All12
scalar rotation root RHSs now account for complete Stock states, actual guarded
requests, narrow typed zero-extension and one/two/four/seven/eight-instruction
fragments. Narrow helpers also expose exact firing traces; previous existential
variants are retained. Explicit traces avoid introducing chosen trace expressions
into root composition. Original mapped source facts supply supported width,
opcode and result type; all six register-count root matches bind canonical
original operands and leave complete state/trace unchanged.

19 public roots normal/MCP standard-only;7 source scans0warnings; current hashes
and evidence:stock-rotate-rhs-checkpoint.json. Earlier rotation checkpoints are
historical. No immediate matching/constant, selected/retained/source or complete
family witness/full-gate claim. Last full batch stock-count-audit.json (428 roots).

Next immediate root matches and original constant/count facts from unchanged
DFG/frame consistency; successful request/type inversion and actual opcode/type/
priority selection. Then original availability-derived write protection, retained
binding and guarded source transfer, complete12-root witnesses (dirty upper bits,
varying amount source types, zero/wrap/masked counts, unmaterialized producers/
constants) and428-prior/seven-final/full gates. All original remaining families/
effects/control/deferred, full simulation/completeness, actual production
integration and fresh complete Stock comparison remain. Full #140 active/
incomplete; production legacy; no commit/push/merge this partial batch.


## Immediate matching and original constant receipts checkpoint

Updated UTC: 2026-10-14T04:41:51.148142+00:00

Eight local/uncommitted modules build through StockRotateImmediateMatch
(390jobs). All six immediate roots now match their actual original count
definition and width-masked amount without requesting a count register.
Successful matching derives the real iconst definition, original DFG value,
canonical environment and unchanged complete state/trace. The normalized
count equals original amount.bits.toNat modulo source rotation width and is
strictly below it, independently of machine materialization. Successful wide
immediate RHS execution also derives its guarded mapped data request internally.

22 public roots normal/MCP standard-only;8 source scans0warnings; hashes/raw
audits:stock-rotate-immediate-checkpoint.json. Previous rotation checkpoints
are historical. No selected/retained/source or complete family witness/gate
claim yet. Last full batch remains stock-count-audit.json (428roots).

Next other successful request/type inversions, deriving narrow source type
from actual extension success and original DFG/frame consistency; actual
opcode/type/priority selection and alias-resolved selected values for all12
roots. Then original availability-derived write protection, retained result
binding/guarded source transfer, complete12-root witnesses (dirty upper bits,
varying count source types, zero/wrap/masked counts, unmaterialized producers/
constants),428-prior/seven-final audits/full gates. All original remaining
family/effect/control/deferred, source/block/whole-driver simulation and
completeness, actual production integration and fresh complete Stock comparison
remain. Full #140 active/incomplete; production legacy; no commit/push/merge.


## Selected immediate original values checkpoint

Updated UTC: 2026-10-14T04:55:44.201030+00:00

Ten local/uncommitted rotation modules build through StockRotateNarrowValues
(392jobs). All six selected immediate roots derive physical/narrow width from
actual matching, original constant count from DFG, guarded mapped data request
from successful execution, exact output/full state and original alias-resolved
values with complete allocation preservation. Narrow input type follows the
actual successful extension and original frame consistency. The narrow
extension/shifts/OR code computes original low bits independently of dirty upper
source bits and preserves every register outside its four-write allocation.

26 public roots normal/MCP standard-only;10 source scans0warnings; current
hashes/evidence:stock-rotate-selected-checkpoint.json. Earlier rotation receipts
are historical. No register-selected/dispatch/retained/source or complete family
witness/full-gate claim. Last full audit stock-count-audit.json (428roots).

Next selected register paths and remaining request/type inversions; actual
opcode/type/priority dispatch and source-by-instruction variants without caller
rule certificates; original availability-derived protection, retained result
binding and guarded source transfer, complete12-root witnesses and428-prior/
seven-final/full gates. All remaining original families/effects/control/deferred,
full source/block/whole-driver simulation/completeness, actual production
integration and fresh complete Stock comparison remain. Full #140 active/
incomplete; production legacy; no commit/push/merge this partial batch.


## Register-request continuation checkpoint

Updated UTC: 2026-10-14T05:08:40.810765+00:00

Eleven saved/uncommitted rotation modules build through StockRotateRegisterRequests
(393 jobs). Successful wide and narrow register roots derive both guarded mapped
source requests. Narrow typing follows actual extension success and original
frame consistency. Pure count-negation preserves the sunk-definition guard.
No new accepted-input condition or oracle was introduced.

29 rotation public roots have normal standard-only axiom sets; all prior26 sets
are unchanged. Three new roots have matching MCP checks;11 source scans report
no warnings. Receipt: stock-rotate-register-checkpoint.json. These are partial
proofs; complete non-vacuity witnesses, selected register original values,
dispatch/retained/source transfer and full batch validation remain required.
Last complete batch remains scalar counts at3221a28 (428 audited roots).

Next selected register original values, deriving internal source protection
from original availability; then actual dispatch, retained/result binding and
guarded original-source transfer, complete12-root witnesses and all full gates.
The entire remaining recovery plan, source/block/whole-driver simulation and
completeness, actual production integration and fresh complete Stock comparison
remain. Full #140 active/incomplete; production legacy; no push/merge.


## Wide register retained/source checkpoint

Updated UTC: 2026-10-14T05:15:44.283457+00:00

Four wide register roots now derive matched width, original source values and
exact full output state, then compose actual retained records/result binding
and guarded original-source transfer. Preliminary-write source protection
follows original availability and actual allocation internally. Source memory
and the demand/availability-restricted post-frame are preserved. Original input
conditions are unchanged. These variants still identify the selected rule;
actual dispatch/source-by-instruction remains required.

14 local/uncommitted rotation modules build421jobs.33 normal standard-only roots;
prior29 sets unchanged; four new matching MCP checks;14 source scans0warnings.
Receipt stock-rotate-wide-source-checkpoint.json. Complete family witnesses and
full gates remain pending; last complete batch3221a28/428 roots.

Next narrow register original values, six immediate retained/source bridges,
actual dispatch/source getters, complete12-root witnesses and428-prior/seven-
final/full gates. All remaining original families/effects/control/deferred,
source/block/whole-driver simulation/completeness, production integration and
fresh complete Stock comparison persist. Full #140 active/incomplete;
production legacy; no commit/push/merge.


## All rotation records/source variants checkpoint

Updated UTC: 2026-10-14T05:24:29.316397+00:00

All12 selected scalar rotation roots now connect actual requests/full state and
original values to retained-record execution/result binding and guarded
original-source transfer. Narrow register7/8-instruction templates handle dirty
upper bits and original masked/negated counts, preserving registers on both
sides of their complete allocation. Original availability derives source
protection internally. Immediate source counts follow original DFG constants.
Source memory and demand/availability-restricted post-frames are preserved.
No original accepted-input condition changed. These variants still identify
the selected rule; actual dispatch/source-by-instruction is required next.

22 saved/uncommitted rotation modules build429jobs.42 normal standard-only roots;
prior33 sets unchanged; nine new matching MCP checks;22 source scans0warnings.
Receipt stock-rotate-record-source-checkpoint.json. Complete non-vacuity witnesses
and full family gates remain pending; last full batch3221a28/428 roots.

Next actual opcode/type/priority dispatch and original getter derivation,
complete12-root witnesses for all public roots,428-prior/seven-final audits and
full build/crates/runtime/encoder/both E2E identity-stage validation. Every
remaining original family/effect/control/deferred, source/block/whole-driver
simulation/completeness, actual production integration across all consumers
and fresh complete Stock comparison persists. Full #140 active/incomplete;
production legacy; no commit/push/merge.


## Rotation dispatch and first complete witnesses

Updated UTC: 2026-10-14T05:36:13.999036+00:00

Actual opcode/type matching identifies one of12 rotation roots internally;
source-by-instruction transfer derives both original restricted operand getters
and selected rule. Prior explicit theorem variants remain available. Eight
left-register actual complete driver/record/source witnesses pass kernel
evaluation:8/16/32/64 × parameter/earlier-producer data, dirty upper bits and
64-bit register count77, with earlier data source registers unmaterialized.

25 compiled modules/46 normal standard-only roots; prior42 sets unchanged; four
new matching MCP checks;25 source scans0warnings. Receipt
stock-rotate-dispatch-witness-checkpoint.json. Right-register witness build is
running in session54864 at checkpoint; revalidate/poll its actual handle.
Three other eight-case witness bodies typecheck with explicit observations in
scratch; final actual kernel checks remain. No complete family/full gate claim.

Next finish pending actual witness evaluations, zero/exact-wrap edge counts and
all-public non-vacuity review; then428-prior/seven-final audits/full gates. All
original remaining families/effects/control/deferred, source/block/whole-driver
simulation/completeness, production integration across all consumers and fresh
complete Stock comparison persist. Full #140 active/incomplete; production
legacy; no commit/push/merge.


## Witness continuation:24 verified base cases

Updated UTC: 2026-10-14T05:47:03.911029+00:00

Right-register and left-immediate eight-case actual driver witness chunks pass
kernel builds (436jobs each).24 base cases verified across previous left
register/current right register/current left immediate: all four widths ×
parameter/earlier-producer data, dirty upper bits and64-bit count77. Immediate
literal-count source registers remain unmaterialized. The new left-immediate
public witness root passes normal/MCP standard-only checks. All28 source files
scan0warnings; pending build files are included only as source scans.

Zero and64 exact-wrap register witness bodies typecheck in both directions
with explicit observations in scratch. Final source has no observation premise
and reuses the parent actual driver observations. Complete64-case witness
plan/checklist covers32 base plus32 register edge cases; edge final kernel
checks remain pending. No family/full-gate completion claim.

Sequential capped queue running in session8546/script
/tmp/driver-resume-rot11-witness-builds.sh: right-immediate, then left-register
edge additions, then right-register edge additions, then428-prior +53-rotation
normal/exact-seven-final trust audit. Revalidate/poll actual handle; no restart
on observation timeout. Full gates are prepared but not started.
Receipt stock-rotate-witness-continuation-checkpoint.json.

Next finish queue, all-public non-vacuity/fresh MCP/source audits and full batch
gates. Every remaining original family/effect/control/deferred, source/block/
whole-driver simulation/completeness, production integration across consumers
and fresh complete Stock comparison persists. Full #140 active/incomplete;
production legacy; no commit/push/merge.


## Full scalar rotation batch validated

Updated UTC: 2026-10-14T06:02:16.057645+00:00

All12 scalar rotation roots now have actual guarded request/type/full-state
proofs, original final-alias values, retained result binding/execution and
guarded original-source transfer. Source-by-instruction derives actual root
selection and both restricted getters internally. Original availability
discharges write protection; original DFG/frame consistency supplies narrow
typing. Old theorem variants/original input conditions remain unchanged.

64 complete actual source/record witnesses cover both directions, four widths,
register/immediate forms, parameter/earlier-producer data, dirty upper bits and
unmaterialized original data/immediate-count registers. Register counts0/64
add zero/exact-wrap edges. The auxiliary witness explicitly inhabits preserved
existential helper variants and the small immediate kernel at8/16/zero.
54 new public roots normal/MCP standard-only;29 source scans0warnings; all428
prior root sets and exact seven final compiler trust sets unchanged in482-root
audit. Full1596/crates1171/runtime4672/0fail/0disagree/seven unchanged known
not-runnable (byte-identical report), encoder1292 identical0different, both
E2E1150accepted0rejected and every identity/stage field equal to prior batch.
Receipt: stock-rotate-audit.json; premise matrix:stock-rotate-witness-checklist.json.

No compiler/default change or fresh complete Stock comparison claim. Inventory
now identifies53 guarded record bridges among517 generated roots; this is not
a completeness percentage. Next uncovered rule families/effects/control/
deferred invariants, then source/block/whole-driver simulation/completeness
and actual production integration across compiler/checker/linker/generated
proof consumers, with original inputs/identities/stages/trust sets preserved
and a fresh complete Stock comparison. Full #140 active/incomplete; production
legacy; local commit next; no push/merge. Earlier rotation checkpoints are
historical and pending states above have been resolved by this full batch.
