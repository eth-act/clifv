# Recovery and continuation plan: test-binary-alignment

Checkpoint: 2026-10-13. Task: [#140](https://github.com/eth-act/clifv/issues/140).
The full objective remains **unfinished**: prove the preserved Stock lowering
driver and switch production while retaining accepted-input and theorem parity.
This file is the resume entry point; the smaller family plans are supporting records.

Latest validated local batch: scalar division/remainder, all ten actual roots
786–795,52 complete original source/record success/trap/boundary cases and824
audited roots (603 prior +221 new). See the
[division receipt](../research/stock-div-audit.json) and final checkpoint below.
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
| Fused binary logical-NOT batch | Landed #180 | `72f2e57`; exact validated `a739ad5` tree, all CI green, no lost matches. Complete NOT-of-XOR/retained/source witnesses and full gates in `stock-logical-not-values-audit.json`. |
| Scalar multiplication and shifts | Landed #181–182 | `40805b7` / `70d187b`; exact validated multiplication/shift trees, all CI green, no lost matches. |
| Subsequent scalar proof families | Fully validated locally | Casts/reduction, source-scope partition, negation, bit reversal/byte swap, unary dispatch and counts; receipts and commits below. |
| Scalar rotations | Fully validated locally | All12 selected roots/retained/source/dispatch,64 complete witnesses,54 new standard-only roots and all full gates; `728cccb`, `stock-rotate-audit.json`. |
| Scalar population count | Fully validated locally (`3ae4c79`) | Four actual roots/retained/source/dispatch,16 complete witnesses,27 new standard-only roots and full gates; `stock-popcount-audit.json`. |
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


## Population-count math continuation

Updated UTC: 2026-10-14T06:20:43.723886+00:00

New StockPopcountMath builds156jobs. Byte extraction, append-based whole-word
byte-count sum and all8/16/32/64 vector-template final arithmetic are kernel
proved; legacy bit-blasting popcnt*_fin variants remain unchanged. Concrete
dirty-upper values/all eight byte indices inhabit these math contracts. Eight
new roots normal/MCP standard-only, one source scan0warnings; receipt
stock-popcount-math-checkpoint.json. No actual root/retained/source or complete
driver-witness/full-gate claim. Last full batch remains728cccb/482 roots.

Next pure SIMD helper closure, all four actual root RHS/request/full-state
proofs, final-alias values/actual selection, retained result binding/original
guarded source transfer, complete actual witnesses and482-prior/seven-final/
full gates. Every remaining original family/effect/control/deferred, source/
block/whole-driver simulation/completeness, production integration across
consumers and fresh complete Stock comparison persists. Full #140 active/
incomplete; production legacy; no commit/push/merge for this partial batch.


## Popcount actual RHS/machine foundations checkpoint

Updated UTC: 2026-10-14T06:39:25.489695+00:00

Four saved/uncommitted modules build385jobs. Checked23-term pure SIMD closure
lifts base-state helpers to Stock while preserving all scheduling fields. Five
actual helper executions compose all four scalar root RHSs, complete mixed-
class3/4-instruction fragments, guarded mapped request and full output state.
Final-alias machine execution computes original low-bit popcount and preserves
registers below/above complete allocation, without source-upper-bit promises.
Local math/RHS/machine witnesses inhabit these foundation contracts.

18 fresh normal/MCP standard-only roots; prior8 math sets unchanged; four source
scans0warnings. Receipt stock-popcount-foundations-checkpoint.json. No actual
selected source/retained/source-transfer/complete-driver-witness/full-gate claim.
Last complete batch remains728cccb/482 roots; production legacy.

Next canonical original matching/request inversion/selected values and actual
opcode/type dispatch; retained binding/original guarded transfer, complete
actual witnesses and482-prior/seven-final/full gates. Every remaining original
family/effect/control/deferred, source/block/whole-driver simulation/completeness,
actual production integration and fresh complete Stock comparison persists.
Full #140 active/incomplete; no commit/push/merge this partial batch.


## Population-count retained/source checkpoint

Updated UTC: 2026-10-14T06:46:12.521216+00:00

Seven compiled popcount modules build423jobs. All four original canonical
matches/success-derived guarded requests/selected original values/full state
and actual opcode/type dispatch now connect retained result binding/execution
to original guarded source transfer. Source-by-instruction derives both getter
and selected root internally; source memory/post-frame preserved.
25 normal standard-only roots; prior18 sets unchanged; seven new matching MCP
checks; seven source scans0warnings. Receipt
stock-popcount-record-source-checkpoint.json. No complete family/full-gate claim.

Two complete eight-case zero/nonzero driver witness bodies precheck with
explicit observations in scratch. Final files have actual kernel observations
and no added observation premise. Sequential capped build queue running in
session78748/script /tmp/driver-resume-pop3-witness-builds.sh: Zero then Nonzero.
Revalidate/poll actual handle; do not restart on observation timeout.

Next finish16 complete actual source/record witnesses, all-public non-vacuity
review,482-prior/seven-final/fresh MCP/source/full gates. All remaining original
families/effects/control/deferred, source/block/whole-driver simulation and
completeness, actual production integration/fresh Stock comparison persist.
Last full batch728cccb/482 roots; full #140 active/incomplete; production legacy;
no commit/push/merge this partial batch.


## Full scalar population-count batch validated

Updated UTC: 2026-10-14T06:55:37.013298+00:00

All four scalar popcount roots now have standard-kernel byte arithmetic,
checked23-term pure SIMD closure/five helper runs, actual guarded RHS/full
states, mixed-class final-alias values/complete allocation preservation,
actual opcode/type selection, retained result binding/execution and original
guarded source transfer. Source-by-instruction derives getter/root internally.
Legacy theorem variants/original input conditions remain unchanged.
16 complete actual source/record witnesses cover zero/nonzero × four widths ×
parameter/earlier-producer data, dirty upper bits and unmaterialized original
producer registers.27 fresh normal/MCP standard-only roots;9 source scans
0warnings; all482 prior root sets and exact seven final compiler trust sets
unchanged in509-root audit. Full1605/crates1171/runtime4672/0fail/0disagree/
seven unchanged known not-runnable (byte-identical report), encoder1292
identical0different, bothE2E1150accepted0rejected and every identity/stage field
equal to prior batch. Receipt stock-popcount-audit.json; premise checklist
stock-popcount-witness-checklist.json.

No compiler/default change or fresh complete Stock comparison claim.
Inventory57 guarded record bridges/517 generated roots is diagnostic only.
Next uncovered scalar families (add/sub/high multiply/division/remaining
casts/logical forms), then memory/call/trap/control/deferred effects, source/
block/whole-driver simulation/completeness and actual production integration
across compiler/checker/linker/generated-proof consumers. Preserve original
inputs/old variants/identities/stages/trust sets/#179 and require fresh complete
Stock comparison. Full #140 active/incomplete; production legacy; local commit
next; no push/merge. Earlier pending popcount checkpoints are historical.

## Add/subtract foundations checkpoint

Five saved, uncommitted `StockAddSub*` modules compile through
`StockAddSubObserved` (387 jobs). All twelve actual positive/negative immediate,
extended and shifted add/subtract RHS forms preserve complete Stock scheduling
state and emit the expected fresh instruction. Successful actual execution
supplies its own mapped-register and demand-safety facts, including extended
source requests. Immediate, shift and extension machine execution uses final
aliases and preserves every register except the fresh destination; extension
semantics uses original narrow values without requiring clean upper bits.
The pure closure excludes demand-changing terms381/434/439; their actual
Stock scheduling is handled explicitly rather than projected away.

Fresh normal kernel and Lean MCP audits agree on23 public roots, all standard
axioms only. Five source scans report zero warnings. Evidence/source hashes,
logs, scripts and preservation archive are recorded in
[stock-addsub-foundations-checkpoint.json](../research/stock-addsub-foundations-checkpoint.json).
This is a partial foundation checkpoint, not completed family validation.

Next: derive canonical environments and looked-through original values from
actual matches; complete actual opcode dispatch including old base variants,
selected original-source values, retained-result binding and guarded source
transfer. Then supply complete actual driver witnesses and every-public-root
non-vacuity review; freshly audit509 prior roots and the exact seven final
compiler trust sets and run full batch gates/identity-stage parity.
All remaining families/effects/control/deferred invariants, source/block/
whole-driver simulation and completeness under original input conditions,
production integration across all consumers and a fresh complete Stock
comparison remain required. Production remains legacy; #140 active/incomplete;
no commit, push or merge for this partial batch.

## Add/subtract original-source checkpoint

Ten uncommitted StockAddSub modules compile through StockAddSubDispatch
(404 jobs). Nine actual positive-immediate, extended and shifted roots now
recover original source values/canonical environments from actual successful
matching and compose selected original binary values through final aliases,
success-derived demand guards and fresh-only machine writes. Narrow extended
inputs retain arbitrary upper bits. Actual opcode dispatch inventories all11
add and6 subtract candidates, including the old base rules and three fused
multiply rules already covered by the prior multiplication batch.

Fresh normal/MCP audits agree on37 standard-only public roots, with all23
foundation axiom sets unchanged. Ten original-source scans report zero warnings.
Receipt and preservation archive:
[stock-addsub-source-checkpoint.json](../research/stock-addsub-source-checkpoint.json).
This is a partial checkpoint; family/full-goal completion is not claimed.

Next: three negative-immediate original-source matching/value connections;
unified selected dispatch/value cases including existing base/multiply variants;
actual retained-result binding and guarded original-source transfer, complete
non-vacuity witnesses,509-prior/exact-seven audits and full validation. All
remaining family/effect/control/deferred, source/block/whole-driver simulation
and completeness, production integration across consumers and fresh complete
Stock comparison obligations persist. Production remains legacy; #140 active/
incomplete; no commit/push/merge for this partial batch.

## Add/subtract retained-record and all-rule source checkpoint

Eighteen uncommitted StockAddSub modules compile through AllSourceValues
(440 jobs). Negative-immediate inversion uses the actual mapped context rather
than substituting identity-context semantics. All twelve new fused forms compose
original values, actual selection, guarded requests, retained result binding,
emitted code, fresh allocation and alias-resolved execution. Original availability
transfer uses the unchanged restricted DFG frame.

Unified availability/source-by-instruction contracts cover all17 actual scalar
add/subtract candidates, including existing base and multiply-fusion variants.
They derive original operands and dispatch internally without a chosen-rule,
final-rule-ID or match-certificate premise. Source memory and the guarded
post-frame relation are preserved; older theorem variants remain available.

Fresh normal/MCP audits agree on54 standard-only public roots;37 prior
checkpoint axiom sets are unchanged. Eighteen source scans report zero warnings.
Receipt and preservation archive:
[stock-addsub-record-checkpoint.json](../research/stock-addsub-record-checkpoint.json).
This remains partial: complete actual driver/source witnesses and per-public-root
non-vacuity,509-prior/exact-seven compiler trust audits and full batch validation
are next. All remaining original family/effect/control/deferred, source/block/
whole-driver simulation/completeness, production integration and fresh complete
Stock comparison obligations persist. Production legacy; #140 active/incomplete;
no commit/push/merge for this checkpoint.

## Add/subtract witnesses continuation

Positive-immediate complete witnesses pass442-job ordinary kernel build
(12 cases: all three roots × four widths), with actual Stock.lower/retained
records/nonempty fresh binding/original source steps, dirty upper bits and
unmaterialized constant register193. The public witness root passes matching
normal/MCP standard-only audits and its original source scan has zero warnings.
Receipt: [stock-addsub-immediate-witness-checkpoint.json](../research/stock-addsub-immediate-witness-checkpoint.json).

Negative and shift complete witness bodies precheck with explicit scratch
observation premises; their final source files contain actual ordinary-kernel
observations and no extra premise.36 compiled observation diagnostics return
true; the sequential22G kernel queue is live, session75070, Immediate then
Negative then Shift. Poll that session or inspect the exact process/log;
do not restart after an observation timeout. Preservation details and live
snapshot are in [stock-addsub-witness-prechecks.json](../research/stock-addsub-witness-prechecks.json).

Priority findings preserved: i8 add of -5 selects higher-priority positive
immediate589/590; i8 subtract of255 selects negative747. Positive witnesses
use127 at every width; negative witnesses retain real narrow-width dispatch.
All36 signed/unsigned extension combinations (six legal width pairs × three
roots × two signs) have successful compiled diagnostics; their complete witness
module is next. Shift zero/wrap edge witnesses, all-public non-vacuity and fresh
509-prior/exact-seven/full validation remain. Gate scripts are prepared but not
started. All original remaining full-goal obligations persist; production legacy;
#140 active/incomplete; no commit/push/merge this partial checkpoint.

## Add/subtract extension/edge validation queue

Immediate, negative and shifted complete driver/source witnesses now pass
ordinary442-job kernel builds (12 cases each). The auxiliary pure projection
has a concrete nonzero-demand/sunk-state witness (407-job build). All four public
witness roots have matching fresh normal/MCP standard-only audits; six witness
source scans have zero warnings.

The36-case extension module covers all six legal target/source width pairs and
both signs for each of the three roots. Its complete original DFG/retained/source
body prechecks with an explicit scratch observation premise; the final source
contains actual ordinary-kernel observations without an extra premise. All36
full observation diagnostics are true. Extension kernel session9291 remains
live. Shift-edge witnesses cover width-equal masked counts at8/16/32 and zero
at64, for each root (12 cases); prechecks and diagnostics pass. Session40997
waits for Extension then compiles ShiftEdge. Session79497 waits for ShiftEdge,
removes eight trailing spaces from StockAddSubObserved and runs the full569-root
validation script. Session75070 is terminal success. Poll these exact handles/
processes; do not restart after an observation timeout.

Sources/hashes, successful checks, pending states, scripts and preservation
archive are in
[stock-addsub-extended-witness-checkpoint.json](../research/stock-addsub-extended-witness-checkpoint.json).
The [witness checklist](../research/stock-addsub-witness-checklist.json) covers
all60 public roots; final all-witness/non-vacuity review remains pending.
Full gates enforce509 prior/exact-seven compiler trust sets plus60 new roots,
full/crates/runtime/encoder/both E2E identity-stage parity. They are queued,
not yet completed. Next finish kernels/gates/fresh all-root MCP/source review,
final receipt and local commit. All remaining original family/effect/control/
deferred, source/block/whole-driver simulation/completeness, actual production
integration/fresh complete Stock comparison obligations persist. Production
legacy; #140 active/incomplete; no commit/push/merge for this partial checkpoint.

## Add/subtract final local validation

All24 modules and84 complete original source/record cases plus auxiliary
projection pass ordinary kernel builds. All17 actual scalar candidates compose
original matching/values, guarded requests, final aliases, retained binding/
code/allocation and availability/source transfer. Source-by-instruction derives
original getters and dispatch internally, preserving old base/multiply variants,
source memory and guarded post-frames.

Full1629/crates1171/runtime4672/0 runnable failures/0 disagreements/seven
unchanged known not-runnable cases/byte-identical runtime report/encoder1292
identical0different/bothE2E1150accepted0rejected pass. Every identity/stage field
matches both modes and population count. All509 prior and exact seven final
compiler trust sets are unchanged in569-root audit;60 fresh normal/MCP roots
are standard-only;24 source scans have zero warnings. All60 public-root premise
reviews and actual non-vacuity chains pass, including original i8 priorities,
dirty upper bits, unmaterialized fused sources, six signed/unsigned extension
width pairs and zero/wrapped shift counts.

Final receipt:
[stock-addsub-audit.json](../research/stock-addsub-audit.json).
Family plan: [stock-scalar-addsub.md](stock-scalar-addsub.md).
The inventory identifies69 guarded record bridges among517 roots; it remains a
diagnostic rather than a reachable-rule completeness percentage. No compiler/
default change or fresh complete Stock comparison is claimed. Next uncovered
high multiply/division/remaining cast/logical families and effects/control/
deferred invariants; source/block/whole-driver simulation and completeness;
actual production integration across compiler/checker/linker/generated-proof
consumers, with fresh complete Stock comparison and final production gates.
Preserve original inputs/old variants/identities/stages/trust sets/#179. Full
#140 active/incomplete; production legacy; local commit next; no push/merge.
Earlier pending checkpoints above are historical and superseded for this batch.

## High-multiply foundations checkpoint

Three uncommitted StockHighMul modules build385jobs.22-term pure helper closure
covers signed/unsigned high multiply, extension and shifts while preserving
all Stock scheduling fields. Actual64-bit helper/root RHSs request the guarded
original sources; alias-resolved execution computes original high products and
preserves every other register. Actual narrow signed/unsigned widening requests
mark their original operands and allocate64-bit temporaries; final shift helpers
also build. Existing narrow arithmetic lemmas are reused unchanged.

Seven new roots plus two existing narrow-math roots have matching fresh normal/
MCP standard-only audits; three original source scans are clean. Preservation
receipt/archive:
[stock-highmul-foundations-checkpoint.json](../research/stock-highmul-foundations-checkpoint.json).
This is partial; no completed family or full-gate claim. Next compose narrow
four-instruction RHS/execution, original canonical matching/success request
inversion/all4-root dispatch, retained binding/source transfer, complete witnesses
and569-prior/exact-seven/full gates. All remaining original families/effects/
control/deferred, whole-driver simulation/completeness, production integration
and fresh complete Stock comparison persist. Last full batch22894a1; production
legacy; #140 active/incomplete; no commit/push/merge for this checkpoint.

## High-multiply narrow composition and dispatch checkpoint

Seven uncommitted StockHighMul modules build393jobs. Both actual narrow RHS
paths compose the real widening requests, multiply, shift and output while
preserving full marked state across four writes. Narrow four-instruction
alias-resolved execution computes signed/unsigned original high products and
preserves registers outside the allocation interval. Its low-level second-source
non-capture condition must be derived internally at the actual record/source
layer; existing stock_lower_available_alias_outside_record supplies the required
original-availability boundary. No additional source-contract premise is accepted.

Original accepted source data and canonical wide/narrow matches build; actual
original opcode/type dispatch derives all four selected roots777–780 internally.
Fourteen public roots have matching fresh normal/MCP standard-only audits; seven
original source scans have zero warnings. Earlier seven root sets are unchanged.
Preservation receipt/archive:
[stock-highmul-composition-checkpoint.json](../research/stock-highmul-composition-checkpoint.json).
This remains partial. Next success-derived helper source types/guards, selected
values and real-record alias non-capture, retained binding/source transfer,
complete non-vacuity witnesses and569-prior/exact-seven/full gates. All remaining
original families/effects/control/deferred, source/block/whole-driver simulation/
completeness, actual production integration/fresh complete Stock comparison
obligations persist. Last full batch22894a1; production legacy; #140 active/
incomplete; no commit/push/merge for this partial checkpoint.

## High-multiply successful requests and actual record intervals

Ten saved StockHighMul modules build396jobs. Successful real widening calls now
supply original guarded mappings/full state; original frame typing/getters exclude
narrow64-bit pass-through internally. Both actual narrow RHS requests derive
source types/guards/mappings and the exact four-write state. Actual wide requests
and output/state are observed. Original source selection derives wide/narrow
roots internally; wide selected values compute the original high product through
final aliases and preserve all other registers.

Actual narrow retained records allocate input+4, including result binding. The
original availability invariant and this derived frontier discharge second-source
non-capture internally, with no additional source-contract premise. Eleven new
public roots have matching fresh normal/MCP standard-only audits; all ten original
source scans have zero warnings. Seven earlier source hashes are unchanged.
Receipt/archive:
[stock-highmul-request-record-checkpoint.json](../research/stock-highmul-request-record-checkpoint.json).
This is partial: complete actual non-vacuity witnesses/premise reviews and full
batch gates have not yet run. Next compose narrow selected machine values using
the internally derived record non-capture, actual retained result binding/code/
execution and guarded original-source transfer; then complete witnesses and569
prior/exact-seven/full batch validation. All uncovered families/effects/control/
deferred, source/block/whole-driver simulation and completeness, production
integration across all consumers and fresh complete Stock comparison persist.
Full #140 active/incomplete; production legacy; last full batch22894a1 local/
unpublished. Saved work preserved; no commit/push/merge for this checkpoint.


## Scalar high-multiply full family validation

All four actual signed/unsigned roots777–780 now compose original typed matching,
derived dispatch, guarded successful helpers/full state, final-alias original
machine values, retained result binding/code/allocation and original demanded-
and-available/source-step transfer. Source-by-instruction derives both getters
and selection internally. Narrow second-source non-capture follows internally
from original availability and the actual four-temporary record frontier; no
extra source-contract premise is accepted. Source memory and post-frame preserved.

Eight complete actual source/record cases cover signed/unsigned8/16/32/64, sparse
original IDs7/31/result100, source values-7/5 and dirty upper machine bits. All34
public-root premise reviews and fresh normal/MCP audits pass with standard axioms;
17 original source scans have zero warnings. All569 prior sets/exact seven final
compiler trust sets unchanged in603-root audit. Full1646/crates1171/runtime4672/
0fail/0disagree/seven unchanged known non-runnable/byte-identical report/encoder
1292identical0different/both E2E1150accepted0rejected pass; all1150 function identity
and stage fields equal both modes and the add/sub baseline.

Final receipt: [stock-highmul-audit.json](../research/stock-highmul-audit.json).
Family plan: [stock-scalar-highmul.md](stock-scalar-highmul.md).
Inventory identifies73 guarded record bridges among517 generated roots; diagnostic
only, not reachable-rule completeness. Next division, remaining casts/logical/
comparison/minmax/select, uncovered effects/control/deferred invariants, source/
block/whole-driver simulation and completeness under original conditions, actual
production integration across compiler/checker/linker/generated-proof consumers,
and fresh complete Stock comparison/final production gates. Preserve original
inputs/old variants/identities/stages/trust sets/#179. Production legacy; full #140
active/incomplete; local commit next; no push/merge. Earlier partial checkpoints
are preserved as history and superseded for this high-multiply batch.

## Division/remainder foundations checkpoint

Five saved uncommitted StockDiv modules build393jobs. A42-term pure helper
closure preserves every scheduling field. Actual signed/unsigned quotient and
multiply-subtract helpers build; actual divisor-zero and three-instruction
signed-overflow guard helpers emit runtime checks while retaining the operand/
original dividend and full state. A generic standard-kernel divisor-minus-one
flag test leaves old fixed-width variants/trust sets unchanged. Helpers are
inhabited at signed/unsigned8/16/32/64 with nonzero demand and sunk fields.

Original accepted source data and actual selected membership cover all ten roots:
udiv786/787, sdiv790/791/788/789 (safe and general), urem792/793, srem794/795.
Nine fresh normal/MCP roots are standard-only; five original scans have zero
warnings; prior high-multiply source hashes are unchanged. Receipt/archive:
[stock-div-foundations-checkpoint.json](../research/stock-div-foundations-checkpoint.json).
This is partial: helper witnesses are not complete original-source records.
Next standard-kernel overflow/intmin arithmetic and actual guard trap/success
semantics, guarded divisor/immediate requests, all ten root matching/selected/
retained/source transfer, complete success/zero/overflow original-source witnesses
and603-prior/exact-seven/full gates. Existing oracle-backed flag lemmas are not
used by these new roots and remain unchanged. All original whole-driver/effect/
production integration/fresh Stock comparison obligations persist; production
legacy; full #140 active/incomplete; validated local tip e56bb87. No commit/push/
merge for this foundation checkpoint.

## Division standard arithmetic and machine guard checkpoint

Eight saved StockDiv modules build396jobs. New standard-kernel integer bounds
prove the actual subtract-one overflow flag at32/64, narrow8/16 shifted intmin,
and signed widening/all-ones reflection. Old fixed-width variants and oracle
proofs remain untouched; new roots do not depend on them. Actual Stock intmin
helpers shift8/16 into a check register and pass32/64 through, retaining every
scheduling field. Minimum-check fragment execution preserves earlier registers.

Actual machine zero and overflow guards now prove both trap and normal outcomes.
Machine witnesses inhabit overflow trap/normal at32/64, zero trap/normal for
signed/unsigned8/16/32/64; original nonzero scheduling helper witnesses extend to
all intmin paths. No nonzero-only source-domain condition is introduced.
Twenty-one fresh normal/MCP public roots are standard-only, including the new
machine execution proofs; all nine earlier division root sets are unchanged.
Eight original source scans have zero warnings; validated high-multiply hashes
unchanged. Receipt/archive:
[stock-div-guards-checkpoint.json](../research/stock-div-guards-checkpoint.json).

This is partial: helper/machine witnesses are not complete original-source
records. Next original guarded divisor/immediate requests and success observations,
all ten canonical root matching/selected/retained binding and original availability/
source transfer, complete source success/zero/overflow witnesses,603-prior/exact-
seven/full gates. All original uncovered families/effects/control/deferred,
source/block/whole-driver simulation/completeness, production integration across
all consumers and fresh complete Stock comparison remain. Production legacy;
full #140 active/incomplete; last full batch e56bb87 local/unpublished. Saved
work/earlier checkpoints retained; no commit/push/merge for this checkpoint.

## Division successful requests and original constants checkpoint

Fourteen saved StockDiv modules build406jobs. Successful immediate materialization
now preserves all scheduling fields via a27-term interpreter projection closure;
no legacy machine-value contract or shared movK_ident edit is used. Successful
real divisor requests expose all five paths: immediate look-through/materialization,
guarded64-bit register, and signed/unsigned guarded widening plus zero check.
Their original mapping/safety and exact complete state follow from execution.
Original mapped context, restricted DFG and source getter connect literal data to
the actual original iconst value; source observations retain that value and the
materialization run. Original public width/mode conditions are unchanged.

Sixteen ordinary-kernel request witnesses use original signed/unsigned division
contexts at8/16/32/64, literals0/9, and validate all five fired helper IDs781–785.
Immediate forward execution with nonzero demand/sunk fields also inhabits the
frame observation. These are original-context helper witnesses, not complete
Stock.lower retained/source-record witnesses. All28 fresh normal/MCP public roots
are standard-only;21 earlier division axiom sets unchanged;14 original source
scans have zero warnings; prior validated high-multiply hashes are unchanged.
Receipt/archive:
[stock-div-requests-checkpoint.json](../research/stock-div-requests-checkpoint.json).

Next standard-only immediate machine values and fragment/result allocation,
all ten canonical root matching/success/selected values, retained binding and
original availability/source success/trap transfer, complete original source/
record success/zero/overflow witnesses,603-prior/exact-seven/full gates. All
original uncovered families/effects/control/deferred, source/block/whole-driver
simulation/completeness, actual production integration and fresh complete Stock
comparison remain. Production legacy; full #140 active/incomplete; last full
batch e56bb87 local/unpublished. Saved work and earlier checkpoints preserved;
no commit/push/merge for this partial checkpoint.

## Division original-source machine-value checkpoint

Eighteen saved StockDiv modules build400jobs. Isolated standard-kernel MOVK
and constant-loading loop proofs establish machine values for all five immediate
materialization rules; legacy IselLcf variants remain untouched. A strengthened
successful divisor observation derives the required immediate fuel bound from
execution. The old theorem remains. Original mapped context, restricted DFG
and getter now yield the original constant's ImmOut machine/fragment/allocation
contract; register/widening paths retain their original guards and complete state.
Sixteen original signed/unsigned8/16/32/64 zero/nonzero request executions
inhabit this stronger source contract without new source conditions.

All40 fresh normal/MCP public roots use only standard axioms;28 prior division
sets unchanged;18 original source scans clean; validated high-multiply source
hashes unchanged. Receipt/archive:
[stock-div-source-values-checkpoint.json](../research/stock-div-source-values-checkpoint.json).
This is partial and not complete source/retained execution. Next all ten actual
root match/RHS composition and alias-resolved machine execution, retained result
binding and original availability/source success/trap transfer, complete source/
record success/zero/overflow witnesses,603-prior/exact-seven/full gates.
All remaining original families/effects, source/block/whole-driver simulation
and completeness, production consumers and fresh complete Stock comparison
remain required. Production legacy; full #140 active/incomplete; last fully
validated local commit e56bb87. Saved work preserved; no push/merge.

## Division actual matcher/RHS checkpoint

All ten division/remainder roots now have canonical forward matches and actual
RHS from-parts composition contracts. General signed division retains zero/
overflow checks; remainder retains divide/multiply-subtract reconstruction;
safe signed constants retain original zero/minus-one exclusions.32 ordinary-
kernel original sparse-ID cases successfully match/execute all ten RHSs across
four operations,8/16/32/64 and literals0/9. These are RHS witnesses, not complete
retained/source execution. Witness and safe-matcher396-job builds pass.
53 fresh normal/MCP roots standard-only;40 previous division sets unchanged;
22 original source scans clean; prior high-multiply hashes unchanged. Evidence:
[stock-div-rhs-checkpoint.json](../research/stock-div-rhs-checkpoint.json).
Next derive canonical environment/helper receipts from actual selection,
alias-resolved machine execution under original demanded/available inputs,
retained result binding/guarded original source success/trap transfer, complete
source/record success/zero/overflow witnesses and603-prior/exact-seven/full gates.
All remaining original families/effects/source/block/whole-driver simulation/
completeness/production integration/fresh Stock comparison obligations persist.
Full #140 active/incomplete; production legacy; e56bb87 local/unpublished.
Saved work/old variants preserved; no push/merge.

## Division selected/retained binding checkpoint

Actual opcode/type matching derives all ten typed root alternatives. Successful
divisor calls internally derive register results. Unsigned division and both
remainder families now derive their canonical selected environments, guarded
source preparations, actual divisor executions, output and complete state from
original source selection. No caller chosen-root/helper execution certificate.
Their retained records derive actual result binding and selected receipts under
original source scope.12 actual whole-driver retained-selection/binding witnesses
cover8/16/32/64; witness batch412jobs passes. These are not complete source
machine execution witnesses. Alias-resolved quotient/multiply-subtract proofs
preserve every nonresult register; four signed/unsigned32/64 alias cases execute
quotient2/remainder1. Final combined proof build416jobs passes.

70 fresh normal/MCP roots standard-only;53 previous division trust sets and22
previous division source hashes unchanged;31 original source scans clean;
validated high-multiply hashes unchanged. Receipt/archive:
[stock-div-selection-checkpoint.json](../research/stock-div-selection-checkpoint.json).
Next actual general/safe signed-division selection and retained receipts, compose
aliased source preparation/zero/overflow guards and quotient/remainder execution,
guarded original availability/result binding/source success/trap transfer,
complete source/record success/zero/overflow witnesses and603-prior/exact-seven/
full validation. Remaining original families/effects/source/block/whole-driver
simulation/completeness/production consumers/fresh complete Stock comparison
are still mandatory. Full #140 active/incomplete; production legacy;
e56bb87 last fully validated local commit. Old variants/saved work preserved;
no push/merge.

## Signed division complete selection/retained receipt checkpoint

General signed RHSs now internally derive guarded dividend preparation, real
divisor execution, minimum-value and overflow checks, output and whole state.
Safe signed RHSs derive guarded preparation and real immediate materialization.
Successful original safe matching derives the actual looked-through literal,
original zero/minus-one exclusions, canonical environment and unchanged frame.
Actual signed source selection and retained records therefore derive both safe/
general paths and result binding internally; no chosen-root/helper certificate.
Eight actual whole-driver signed fixtures check all four original root IDs at
8/16/32/64. With12 earlier unsigned/remainder fixtures, all ten real roots have
retained-selection/binding witnesses. These are not complete source execution.

Zero/overflow fragments now execute through final aliases with both trap and
normal outcomes; zero alias witnesses cover signed/unsigned8/16/32/64, overflow
alias witnesses32/64. New source machine composition remains separate.
Signed witness kernel build416jobs (180s) and final combined421jobs pass.
86 fresh normal/MCP roots standard-only;70 prior trust sets and31 prior sources
unchanged;39 original source scans clean; validated high-multiply hashes unchanged.
Receipt/archive:
[stock-div-signed-selection-checkpoint.json](../research/stock-div-signed-selection-checkpoint.json).
Next compose aliased source preparation/constant materialization/zero/overflow
checks/quotient/remainder execution, guarded original availability/result binding/
source success/trap transfer for all ten roots, complete original-source success/
zero/overflow witnesses and603-prior/exact-seven/full gates. All original remaining
families/effects/source/block/whole-driver simulation/completeness/production
integration/fresh complete Stock comparison obligations persist. Full #140
active/incomplete; production legacy; e56bb87 last fully validated local commit.
Old variants and saved work preserved; no push/merge.

## Division original operands/guards/body execution checkpoint

Internal alias semantics inherits refinement. Actual driver alias idempotence,
under the original scope/dominance conditions, derives the invariance required
by existing renaming machinery internally. No semantic-invariance premise is
added to the original source contracts. All five immediate paths execute through
final aliases with full scheduling and outside-allocation register preservation.
Five ordinary-kernel witnesses check actual fired IDs; LCF32 uses305419896 and
LCF64 uses81985529216486895, exercising actual MOVK paths at both machine sizes.
Original mapped context/restricted DFG/getter derives correct original constants
for unmasked general and masked safe materialization paths.

Actual divisor calls compose original constants or64-bit source registers or
narrow extension paths with alias-resolved zero checks. Both original source
zero-trap and nonzero normal outcomes are proved.16 original-context actual
signed/unsigned8/16/32/64 literal0/9 divisor-fragment witnesses include dirty
upper bits. Actual extended/plain dividend requests establish original operands
through aliases, with eight widening/pass-through and one unsigned64 plain
witness. Quotient and divide/multiply-subtract bodies establish successful
original source results; eight signed/unsigned negative-numerator cases cover
8/16/32/64 and unaffected-register preservation. These are component executions,
not complete retained original-source instruction execution witnesses.

Final combined413-job proof build passes;103 fresh normal/MCP public roots use
standard axioms only;86 previous trust sets and39 previous source hashes unchanged;
49 original source scans clean; validated high-multiply hashes unchanged. Evidence:
[stock-div-operands-body-checkpoint.json](../research/stock-div-operands-body-checkpoint.json).
Next derive noncapture/held-value transfer from actual original availability and
record allocation intervals, compose all ten selected operand/zero/overflow/body
executions, retained result binding/original source success/trap transfer,
complete retained original-source success/zero/overflow witnesses,603-prior/exact-
seven/full gates. Remaining original families/effects/source/block/whole-driver
simulation/completeness/production consumers/fresh complete Stock comparison
remain mandatory. Full #140 active/incomplete; production legacy; e56bb87 last
fully validated local commit. Old variants/saved work preserved; no push/merge.


## Unsigned64 retained source composition build checkpoint

Division composition status: active; full #140 remains incomplete. Branch agent/stock-logic-not-values-pr, HEAD e56bb87 local/unpublished, worktree driver-proof-resume. The immediate unsigned64 source-transfer build failure (unavailable getAs_of_regs helper) is fixed using its elementary getter proof. Source-transfer target passes453 jobs; actual whole-lowering unsigned64 success and zero-trap witness target passes456 jobs, including ordinary-kernel lowering fixtures. New composition modules remain local/uncommitted; full new-root audits and the division-family batch gates remain pending. Prior103-root checkpoint remains the latest complete division audit. Execution has been too fragmented across small proof/audit slices; no established permission or contributor blocker. Next: finish source/record composition and complete witnesses across the remaining nine division roots, then full family validation; all original remaining families/effects, block/whole-driver simulation/completeness and compiler/checker/linker/generated-proof production integration remain required. Production still legacy. Old saved work preserved; no push/merge. UTC 2026-10-14T13:48:53.755059+00:00


## Unsigned division retained original-source execution checkpoint

Actual unsigned division now composes original source operands, zero guards and
quotient execution through final aliases at8/16/32/64. Original availability and
record allocation intervals derive operand noncapture internally; caller source
conditions remain preserved. Actual retained binding derives output registers,
fresh bounds and emitted code. Original successful source steps preserve the
updated frame, demanded available values and memory; original zero traps remain
covered. Common unsigned source entry derives operand getters and wide/narrow
choice internally. Eight complete actual Stock.lower source/record witnesses
cover success and zero traps at all four widths with dirty upper bits.

Combined466-job proof build passes.131 normal roots standard-only;28 new MCP
roots standard-only;103 prior axiom sets and49 prior original source hashes
unchanged;65 original source scans clean; validated high-multiply hashes unchanged.
[Receipt](../research/stock-div-udiv-composition-checkpoint.json).
Archive /home/lee/.clifv-recovery/20261014T140444Z/stock-div-udiv-composition-checkpoint.tar.gz.
The unsigned checkpoint excludes subsequent remainder work. Signed/unsigned
remainder selected/retained/source-entry proofs now build; complete original
remainder witnesses are being validated sequentially. Signed division general/
safe source composition, zero/overflow/full witnesses and full family gates
remain required. All original uncovered families/effects, source/block/whole-
driver simulation/completeness and compiler/checker/linker/generated-proof
production integration/fresh complete Stock comparison persist. Full #140 active/
incomplete; production legacy; e56bb87 last fully validated local commit.
Saved work and old variants preserved; local/uncommitted; no push/merge.


## Unsigned division and signed/unsigned remainder original-source checkpoint

Division unsigned/remainder original-source checkpoint: active; full #140 incomplete. Branch agent/stock-logic-not-values-pr, HEAD e56bb87 local/unpublished, worktree driver-proof-resume. All six actual unsigned-division/signed-or-unsigned-remainder roots now have selected/retained/source execution and binding transfers. Shared original-source trap entries derive operand getters and semantic failure internally. Original availability/allocation derives noncapture; original held/available-value guards, frame updates, memory preservation and zero traps retained. Eight unsigned-division success/zero witnesses plus16 remainder success/zero witnesses cover8/16/32/64; eight signed minimum/zero and minimum/minus-one remainder boundary witnesses prove minus-one returns zero without source restriction. Source overflow reflection/alias helper has witnesses at all four widths; actual signed-division general/safe source composition is still pending.
Combined 518-job proof build;182 standard-only normal public roots;51 new standard-only MCP roots.131 previous trust sets/65 original source hashes unchanged;94 original source scans clean; validated high-multiply hashes unchanged.23 initial MCP transport timeouts were retained and retried successfully against a compact project-local import audit at limited concurrency, with original-source scans separate; no witness build restarted. Receipt docs/research/stock-div-rem-source-checkpoint.json; archive /home/lee/.clifv-recovery/20261014T142722Z/stock-div-rem-source-checkpoint.tar.gz. Unsigned-only receipt and all earlier snapshots preserved.
Next: compose general/safe signed-division preparations/minimum/overflow/quotient through final aliases; retained binding and guarded original source successes/traps; complete original-source witnesses at8/16/32/64 including zero and overflow; then full division603-prior/exact-seven/build/crates/runtime/encoder/both E2E identity-stage gates. All original uncovered families/effects, source/block/whole-driver simulation/completeness, production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain mandatory. Production legacy; IselLcf/T6 untouched; saved work/old variants preserved; local/uncommitted; no push/merge. UTC 2026-10-14T14:28:26.878804+00:00


## Scalar division/remainder full local validation

All ten actual roots786–795 now have original selected/retained/source execution
and binding transfers: unsigned division, general and safe signed division,
signed and unsigned remainder, narrow8/16/32 and wide64. Minimum/zero/overflow
preparation, exact helper states, final aliases, complete fresh-write frames,
original constant definitions and source results are connected. Original scope/
dominance/restricted DFG/demanded-and-available conditions remain; getters, chosen
root/helper runs, noncapture, alias/bound/constant/result facts derive internally.
Old theorem variants and IselLcf/T6 remain untouched.

52 complete original source/record witnesses include normal and zero outcomes,
signed minimum/zero and overflow, signed minimum/minus-one remainder returning
zero at every width, and negative safe quotients with constants unmaterialized.
Full1768/crates1171 pass; runtime4672 with zero failures/disagreements and seven
unchanged unsupported cases; encoder1292 identical/zero differences. Both E2E
modes1150 accepted/zero rejected and every identity/stage field unchanged from
high multiplication; runtime report byte-identical.824 normal roots retain all
603 prior sets and exact seven final compiler trust sets;221 new standard-only
MCP roots,122 original clean scans. Earlier checkpoint timeouts were resolved by
bounded compact-import audit; fresh final221-root MCP checks have zero failures.
Receipt [stock-div-audit.json](../research/stock-div-audit.json); family plan
[stock-scalar-division.md](stock-scalar-division.md). Local commit is recorded in
#44. No compiler/default change; no push/merge. Full #140 active/incomplete.

Next uncovered families: comparison/minmax/select and remaining scalar logical/
cast forms, then original effects/memory/calls/atomics/traps/control obligations.
Original source/block/whole-driver simulation and completeness, production
integration across compiler/checker/linker/generated-proof consumers and a fresh
complete Stock comparison remain mandatory. Do not substitute scalar family
completion for the full goal.


## Comparison standard-kernel arithmetic and machine-body checkpoint

Comparison foundation checkpoint active; full #140 incomplete. HEAD0108129 local/unpublished, branch agent/stock-logic-not-values-pr, driver-proof-resume. Five local uncommitted StockCmp modules. Standard-kernel zero/carry/signed greater-or-equal and all ten comparison conditions include both signed overflow regions; signed/unsigned extensions, guarded predecessor rewrites and condition inversion preserve legacy native variants. Alias-resolved compare/cset implements original bool8 at8/16/32/64 and preserves all other registers; ten conditions/four widths/six boundary machine-body witnesses use distinct nonidentity aliases. Pure29-term builder closure preserves full scheduling fields; six real constructor/condition/output-helper witnesses pass. Combined373-job proof build;17 normal/fresh compact-import MCP roots standard-only;five original clean scans;validated division122 sources unchanged. Receipt docs/research/stock-cmp-foundation-checkpoint.json; archive /home/lee/.clifv-recovery/20261014T154835Z/stock-cmp-foundation-checkpoint.tar.gz.
These are machine-body/pure-builder foundations, not complete Stock.lower comparison source/record execution. Actual652 emitter requests/constant/zero/predecessor/register/extension/i128 cases and715 shape/frame/execution remain next. Full715 closure includes effectful opportunistic-definition/register requests, so pure29-term scope does not cover arbitrary715 calls; derive guarded shape-specific actual executions. Then original comparison/fused-extension matching/selection/retained binding/source transfer, complete original witnesses; minmax/select;824-prior/exact-seven/full gates. All original remaining families/effects/source/block/whole-driver simulation/completeness/production compiler/checker/linker/generated-proof integration/fresh complete Stock comparison remain mandatory. Production legacy; IselLcf/T6 untouched;saved work/old variants preserved; no push/merge. UTC 2026-10-14T15:49:03.349101+00:00


## Comparison condition and register-emitter checkpoint

Updated UTC: 2026-10-14T16:37:38.962576+00:00

- Local HEAD remains `01081291`; branch `agent/stock-logic-not-values-pr`, unpublished. All earlier snapshots are preserved.
- Eleven `StockCmp*.lean` modules compile together (397 jobs). All33 public roots pass normal kernel/transitive and fresh compact-import MCP axiom audits using only standard axioms. Eleven original source scans are clean. The ten prior condition sources and all122 validated division sources retain their checkpoint hashes.
- Actual condition-result715 Zero/NotZero and explicit-flag executions derive their real compare/cset, fresh output and complete Stock state. Final-alias execution preserves the boolean result and other registers without a semantic-invariance premise. Actual helper witnesses cover both boolean outcomes, both machine widths, every explicit condition, nonidentity aliases and dirty upper bits.
- Actual register-emitter `rule_inst_5128.rhs` success derives both original source demand guards and mapped registers internally, and exposes its exact flag producer and complete double-marked state. Its non-vacuity witnesses cover both widths and all conditions with distinct mapped operands.
- Evidence: `docs/research/stock-cmp-condition-register-checkpoint.json`; archive `/home/lee/.clifv-recovery/20261014T163738Z/stock-cmp-condition-register-checkpoint.tar.gz`. Earlier foundation and condition checkpoint receipts remain historical evidence.
- This is an incremental proof checkpoint. It is not a completed comparison family or a fresh full-repository gate run. The last fully validated family remains division. Production remains legacy.
- Next: original source comparison selection/matching, all effectful652 zero/constant/predecessor/extension/register cases under original conditions, retained-record/result binding and guarded source transfer, fused comparison extension, complete original Stock.lower witnesses, minmax/select and full family gates. Original effects, deferred sinking invariant, source/block/whole-driver simulation and completeness, production compiler/checker/linker/generated-proof consumers and fresh complete Stock comparison remain mandatory. No push or merge.


## Original comparison source selection checkpoint

Updated UTC: 2026-10-14T16:44:32.432298+00:00

- Thirteen local comparison modules compile together (402 jobs). All36 public roots pass normal kernel/transitive and fresh compact-import MCP checks with only standard axioms; thirteen original source scans are clean. All122 validated division sources and ten prior condition sources remain byte-identical to saved checkpoints.
- `StockCmpSourceMatch.lean` derives original accepted source data, scalar width and boolean result type, and proves actual source selection is root958. These follow from the original mapped context and original source instruction, without replacing the original input scope.
- `StockCmpSourceMatchWitness.lean` inhabits these contracts with an actual successful named Stock lowering call from a built, accepted original function with source IDs7/31/100. This is a named-root/source-selection witness, not yet a complete retained-record/source-step Stock.lower witness.
- Receipt: `docs/research/stock-cmp-source-selection-checkpoint.json`; archive `/home/lee/.clifv-recovery/20261014T164432Z/stock-cmp-source-selection-checkpoint.tar.gz`. HEAD remains local/unpublished `01081291`; all comparison files and receipts are uncommitted. Production remains legacy; the full goal remains active and incomplete.
- Next theorem: derive the canonical comparison root environment and unchanged match state from actual matching, then derive all actual emitter652 zero/constant/predecessor/register/extension executions and original values. Use original accepted-width/type facts to discharge incompatible i128 branches. Connect condition715/output172, actual retained-record binding and guarded source transfer. Complete original Stock.lower comparison/fused-extension witnesses and minmax/select, then run the full family gates preserving all824 prior public roots and exact seven final compiler trust sets.
- All original remaining effects and deferred-sinking invariants, source/block/whole-driver simulation and completeness, production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain required. No compiler/default edit, commit, push or merge occurred in this checkpoint.


## Canonical comparison matching and register source-value checkpoint

Updated UTC: 2026-10-14T17:15:22.859022+00:00

- Local HEAD remains unpublished `01081291`, branch `agent/stock-logic-not-values-pr`; nineteen comparison modules and receipts are uncommitted. All earlier snapshots and source files are preserved.
- `StockCmpRootMatch.lean` supplies actual comparison root matching and its successful observation: original operand type, canonical environment, full unchanged state and trace. `StockCmpSelectedCalls.lean` derives actual root958, canonical match and all real emitter652/condition715/output172 calls from original first-match selection, including internal fuel bounds and intermediate states. `StockCmpSelectedCallsWitness.lean` inhabits these from the already compiled actual named original-source lowering witness.
- `StockCmpRegisterValues.lean` composes actual guarded register-emitter RHS5128 and condition715 executions into original32/64 comparison bool8 through final aliases, with full fresh-result code and every other register preserved. Actual RHS success supplies guards/maps; demand monotonicity and original getters supply source values; no caller producer certificate or semantic-invariance premise is added.
- `StockCmpRegisterValuesWitness.lean` covers both source machine widths and all ten conditions using a built accepted sparse-ID7/31/100 original context, original getters, dirty upper machine bits and nonidentity final aliases192→1/193→3. This remains a real RHS/helper composition witness, not a complete retained-record/source-step Stock.lower witness. `StockCmpExtendBuilder.lean` adds actual pure393 builder/full-state observation and its sparse-register witness for later narrow comparison emission.
- Combined target build passes408jobs. All46 public roots pass normal kernel/transitive and fresh compact-import MCP audits with standard axioms only. Nineteen original scans are clean; all36 prior comparison axiom sets, thirteen prior comparison source hashes and122 validated division sources are unchanged. `git diff --check` passes. Receipt `docs/research/stock-cmp-register-source-values-checkpoint.json`; archive `/home/lee/.clifv-recovery/20261014T171522Z/stock-cmp-register-source-values-checkpoint.tar.gz`.
- Witness elaboration initially timed out while reducing the entire symbolic fixture context; opacity for the built context and symbolic condition-code facts preserve the same statements and reduce the final witness target build to2.6s. No heartbeat limit increase, unchecked decision procedure or additional axiom was used.
- Next: connect actual emitter652 first-match execution to all original source-value alternatives (register, constant, predecessor, zero and narrow extension); then condition/output composition, actual retained-record/result binding, guarded original-source transfer, fused comparison extension and complete Stock.lower witnesses. Complete minmax/select and full comparison family gates preserving all824 prior audited roots and exact seven final compiler trust sets.
- Full #140 remains active/incomplete. Last fully validated family remains division; full comparison family gates are not claimed. Production remains legacy. All original remaining effects/deferred-sinking invariants, source/block/whole-driver simulation and completeness, production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain required. No compiler/default edit, commit, push or merge occurred.


## Actual parameter comparison records and original source transfer

Updated UTC: 2026-10-14T18:09:48.453792+00:00

- Local/unpublished HEAD remains `01081291`, branch `agent/stock-logic-not-values-pr`;29 comparison modules are local/uncommitted. No compiler/default edit, commit, push or merge.
- `StockCmpRegisterSelection.lean` proves actual652 first-match selection for original32/64 parameter operands; it excludes constant/zero/i128 alternatives and refutes later narrow fallbacks using their rejected-prefix failure of the real earlier register rule. No caller-selected emitter RHS certificate is required.
- `StockCmpRegisterTraceValues.lean` adds an independent condition-trace prefix variant, preserving the prior trace-equal theorem. It accommodates the real emitter rule appended before715. `StockCmpOutput.lean` derives actual output172 vector and full unchanged state.
- `StockCmpParameterValues.lean` and `StockCmpParameterRootValues.lean` compose actual emitter/condition/output into original32/64 source bool8 through final aliases and fresh writes. `StockCmpParameterRootWitness.lean` inhabits the real named root execution and complete output/value frame.
- `StockCmpParameterRecordValues.lean` derives actual retained-record selection, result binding/copy absence, emitted code and value preservation; its availability variant retains original restricted DFG and demanded-and-available guards. `StockCmpParameterSourceValues.lean` transfers to the real original SourceInstResult frame and preserves source memory, with getter-explicit and internally derived-getter variants retained.
- `StockCmpParameterDriverRuns.lean` contains a normal kernel proof of actual complete Stock.lower execution retaining root958/context/source identities and stable parameter aliases. `StockCmpParameterDriverWitness.lean` supplies a complete64/eq retained/source-step witness with sparse source IDs7/31/100, real nonempty binding, dirty upper input bits, fresh boolean result, other-register preservation and the original guarded source relation. This is one complete case in the parameter path; it is not a completed full comparison family.
- Combined build419jobs passes. All61 public comparison roots pass normal kernel/transitive and fresh compact-import MCP audits with only standard axioms. All29 original scans are clean. The prior19 comparison source hashes/46 trust sets, earlier comparison checkpoints and all122 validated division sources remain unchanged. `git diff --check` passes.
- Receipt `docs/research/stock-cmp-parameter-driver-checkpoint.json`; archive `/home/lee/.clifv-recovery/20261014T180948Z/stock-cmp-parameter-driver-checkpoint.tar.gz`. The aggregate audit includes the nested ParameterDriverWitness namespace rather than assuming a flat theorem namespace. Saved work and historical snapshots are retained.
- Next: original emitter652 defined/register operands and constant/zero/predecessor/narrow8/16/extended alternatives, their internally derived type/value facts and full root/retained/source compositions; fused comparison extension, minmax/select, complete family witnesses and full family gates preserving all824 prior roots/exact seven final compiler sets. The parameter helper's context-type/no-definition facts identify that path; they are not replacements for the original full-goal input conditions.
- Full #140 stays active/incomplete; production remains legacy. Whole-family/full repository gates are not yet claimed; division remains the last fully validated family. All original uncovered effects/deferred sinking invariants, source/block/whole-driver simulation/completeness, compiler/checker/linker/generated-proof production integration and fresh complete Stock comparison remain mandatory.


## General nonconstant comparison selection and defined-source execution

Updated UTC: 2026-10-14T18:38:53.267382+00:00

- HEAD remains local/unpublished `01081291`, branch `agent/stock-logic-not-values-pr`;36 comparison modules are uncommitted. All prior work and theorem variants remain preserved. No compiler/default edit, commit, push or merge.
- `StockCmpNonconstantSelection.lean` extends actual652 first-match selection from parameters to original defined nonconstant source operands. `NonConstantSource` refers to the original defining CLIF instruction; mapped source data excludes constant look-through cases, and the earlier register match excludes later narrow fallbacks. It introduces no caller-selected emitter/RHS certificate.
- The nonconstant emitter/root/retained-record/source modules retain the real emitted-rule trace, derive output/binding/code internally and preserve original availability-restricted DFG, demanded/available guards and real SourceInstResult frames. Getter-explicit and automatically derived-getter variants are retained alongside the earlier parameter variants.
- `StockCmpNonconstantDriverRuns.lean` normally kernel-checks actual Stock.lower of `ineg64 v7 → v31; icmp.eq64 v31 v7 → v100`. The actual reverse scan allocates comparison result195 before negation result196, so the final alias is193→196. This was inspected from actual execution and then kernel-proved; no hard-coded assumed alias is used as evidence.
- `StockCmpNonconstantDriverWitness.lean` supplies a complete actual retained/source-step witness at statement1 using original defined value−7 and parameter7, dirty upper machine bits, real nonidentity alias193→196, nonempty source-result binding, fresh boolean and original guarded source transfer. The defining negation satisfies original DFG consistency and its value is materialized through the actual final alias.
- Combined build426jobs passes. All71 public comparison roots pass normal kernel/transitive and fresh compact-import MCP audits with only standard axioms. All36 original scans are clean. Prior29 comparison source hashes/61 trust sets, earlier checkpoints and122 validated division sources remain unchanged. `git diff --check` passes. Receipt `docs/research/stock-cmp-nonconstant-driver-checkpoint.json`; complete archive `/home/lee/.clifv-recovery/20261014T183853Z/stock-cmp-nonconstant-driver-checkpoint.tar.gz`.
- Next: constant/zero/predecessor and narrow8/16/extended comparison alternatives under original source facts, internally derived type facts, fused comparison extension, minmax/select, complete family witnesses and full family gates preserving all824 prior roots and exact seven compiler trust sets. Nonconstant classification and current32/64 type facts identify a path; they do not replace the original full-goal input conditions.
- Full #140 remains active/incomplete; production remains legacy. Full comparison family gates are not claimed; division remains the last fully validated family. All original remaining effects/deferred-sinking invariants, source/block/whole-driver simulation/completeness, production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain required.


## Immediate comparison source-value checkpoint

Updated UTC: 2026-10-14T18:55:46.674507+00:00

- Local unpublished HEAD remains01081291. Four additional comparison modules bring the targeted build to40modules/439jobs and78 public roots. All78 normal kernel/transitive and fresh compact-import MCP audits use only standard axioms; all40 original source scans are clean. Prior36 comparison source hashes/71 axiom sets and122 validated division source hashes are unchanged.
- Actual RHS5165 success derives the original guarded source request, mapped register, exact immediate flag producer and full marked state. Actual condition715 execution yields the immediate machine predicate through final aliases with every other register preserved.
- Original restricted DFG consistency and source getters connect the encoded immediate to the original defining constant, composing real RHS/condition calls into original32/64 comparison bool8. The original constant need not occupy a machine register.
- Real helper witnesses cover both machine widths/all conditions; condition-value witnesses cover both shifted and unshifted encodings, dirty upper bits and nonidentity aliases. Complete source-value non-vacuity and actual Stock.lower immediate record witnesses remain pending, so this is not a completed family.
- Receipt: docs/research/stock-cmp-immediate-checkpoint.json. Archive: /home/lee/.clifv-recovery/20261014T185522Z-immediate/checkpoint.tar.gz
- Next: actual652 immediate first-match observation and source typing; derive root/retained binding/guarded original source transfer internally, then complete original immediate witnesses. Continue zero/predecessor/narrow/extended/fused comparisons and minmax/select, then full family gates preserving824 prior roots and exact seven compiler trust sets.
- Full #140 remains active/incomplete. Production remains legacy. Remaining effects/deferred-sinking invariants, source/block/whole-driver simulation and completeness, compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain mandatory. No push or merge.


## Actual immediate driver run and integration work

Updated UTC: 2026-10-14T19:38:22.982720+00:00

- Actual Stock.lower of original iconst64 v31=3; icmp.eq64 v7 v31→v100 passes ordinary kernel checking. The comparison is retained at statement1/root958, original context and constant data are preserved, demand31 is zero and original input aliases are unchanged. Actual execution inspection shows the constant record is omitted and comparison result195 is allocated.
- The original source/frame/DFG/dominance/availability and dirty-machine-register witness inputs typecheck independently. Source constant3 is deliberately absent from the machine register for its source mapping (that machine register contains777); its zero demand discharges the original guarded relation.
- Normal79-root audit preserves all78 prior comparison trust sets; the new driver observation passes fresh MCP with standard axioms only. All40 prior comparison source hashes remain unchanged. Receipt: docs/research/stock-cmp-immediate-driver-observation.json; archive: /home/lee/.clifv-recovery/20261014T191921Z-immediate-driver/evidence.tar.gz
- Six new selection/emitter/root/record/transfer/complete-witness modules are prepared but remain unvalidated. General selection initially exhausted heartbeats; the revised proof uses a protected original constant-data fact, direct prefix rejection and a separately checked successful-match/RHS lemma. Its integration build is the next check. No full-family or full-repository gate is claimed.
- Next: finish general immediate selection and validate the dependent record/source/complete-witness chain, then remaining zero/predecessor/narrow/extended/fused comparisons and minmax/select, complete family witnesses and full gates. All remaining families/effects/deferred sinking, source/block/whole-driver simulation and completeness, actual production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain mandatory. Full #140 is active/incomplete; production legacy; local/uncommitted; no push/merge.


### Immediate selection performance diagnosis

Updated UTC: 2026-10-14T20:03:02.659478+00:00

The general selection/integration proof remains unvalidated. Profiling a scratch copy isolates recursive inverse simplification as the costly step. Supporting protected original-data/match/RHS lemmas typecheck independently; match and RHS executions are preserved while decoding their exact source facts. The revised decoder uses the ten relevant term facts rather than the full generated metadata context. Current build log: /tmp/driver-resume-cmp-immediate-chain-sparse.log (session53099; recheck authoritative process before waiting/restarting). Prepared47-module/88-root audit is not a passed audit. Prior79-root observation evidence and all saved work are preserved. Finish this chain, then every remaining original full-goal obligation; production legacy; no push/merge.


### Protected original immediate conclusion

Updated UTC: 2026-10-14T20:19:38.473067+00:00

Authoritative failure output identified a specific proof failure: inverse simplification at all locations rewrote the theorem's target RHS equation into existential interpreter assertions. A private protected conclusion and explicit elimination lemma now preserve the original public theorem statement during decoding; all supporting helpers typecheck independently at the unchanged4M limit. Two explicit decoding passes replace recursive inverse decoding. The integration build remains unvalidated; session60219/log /tmp/driver-resume-cmp-immediate-chain-bounded-outcome.log must be rechecked against its actual process. All40 prior validated comparison source hashes remain unchanged. Evidence: docs/research/stock-cmp-immediate-outcome-progress.json. No88-root/full-family/full-repository gate is claimed. Finish general selection and dependent retained/source/complete-witness chain, then every original remaining full-goal obligation. Production legacy; no push/merge.

The session60219 build is now terminal (exit1), not a verified wait. Selection reached explicit type mismatch at line240; inspect /tmp/driver-resume-cmp-immediate-chain-bounded-outcome.log before the next edit. No dependent integration gate passed.


### Raw extractor conversion and zero-case discharge

Updated UTC: 2026-10-14T20:50:31.701985+00:00

Three checked raw-extractor conversion helpers derive original constant lookups and exclude original nonconstant/normalized-nonzero zero matches. Actual remaining-goal diagnostics fall from24 to16: all eight32/64 zero-case goals are discharged; two direct-immediate and fourteen later-rule goals remain. Rejection application diagnostics expose unconstrained fuel/after/start-state inference; original start state/trace are now explicit, but prefix witness extraction still needs resolution. General selection and its dependent record/source/witness chain remain unvalidated. All40 prior source hashes are unchanged. Evidence docs/research/stock-cmp-immediate-extractor-progress.json. Next: derive the exact recorded prefix failure with explicit witnesses, then finish actual direct matching/output, validate the full prepared chain and complete every remaining original full-goal obligation. Production legacy; no push/merge.


## Integrated original immediate comparison path

Updated UTC: 2026-10-14T21:00:45.835606+00:00

- General actual652 first-match selection now derives rule5165 from original nonconstant-X/nonzero encodable-Y classification. All eight zero cases are excluded from original extractor/source facts; all later candidates are excluded from actual recorded failed-prefix matches. A private protected conclusion preserves the original public statement while decoding; normalized prefix facts and explicit match-start state avoid the diagnosed proof failures.
- Actual emitter/condition/output source values, selected-root execution, retained-record/result binding/copy absence, guarded original-source transfer and auto-getter variants all compile. No caller-selected RHS/helper/output/binding certificate is added. Original restricted DFG, availability, demanded-and-available guards, scope and dominance are retained.
- Complete actual original64/eq Stock.lower retained/source-step witness passes with sparse IDs7/31/100, dirty upper bits, fresh result195 and source constant3 deliberately absent from its mapped machine register193 (which contains777). Actual immediate execution yields original bool8 and preserves the other machine registers and source memory/frame relation.
- Combined47-module build passes446jobs. All88 public roots pass normal kernel/transitive and fresh compact-import MCP audits using only standard axioms. All47 original scans are clean. Prior40 comparison source hashes/78 trust sets, the earlier79-root driver observation and122 validated division source hashes remain unchanged. git diff --check passes.
- Receipt docs/research/stock-cmp-immediate-integrated-checkpoint.json; complete archive /home/lee/.clifv-recovery/20261014T205920Z-immediate-integrated/checkpoint.tar.gz. Local/unpublished HEAD remains01081291; comparison sources remain uncommitted. Earlier failed/profiling receipts remain historical; this receipt supersedes their unvalidated immediate-path status.
- This is an integrated path checkpoint, not completed comparison-family/full-repository validation. Division remains the last fully validated family. Next: original zero/predecessor, nonencodable/constant-LHS/both-constant, narrow8/16/extended/fused/composite-condition alternatives; complete original witnesses across all forms/widths/boundaries; minmax/select and full comparison-family gates preserving824 prior roots/exact seven compiler trust sets.
- Full original #140 is active/incomplete. Remaining uncovered families/effects/deferred sinking, source/block/whole-driver simulation and completeness, actual production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain mandatory. Production legacy; no push/merge.


## Zero/nonzero helper selection and original source values

Updated UTC: 2026-10-14T21:32:57.475021+00:00

- Actual649 Zero/NotZero inversion and successful observation preserve complete Stock state; helper witnesses cover both machine widths. Real4979 nonzero64 RHS performs the original guarded source request and derives its map, exact condition and full marked state from success.
- Actual651 first-match selection on original64-bit parameters derives real RHS internally, excluding higher second-result look-through and incompatible widths. Actual651/715 inequality-to-zero and651/649/715 equality-to-zero executions hold original parameter bool8 through final aliases, deriving requests/code and preserving every other register.
- Original accepted sparse-ID7 parameter function helper/source-value witnesses cover both boolean outcomes for equality and inequality, real651 selection/inversion/715 calls, dirty upper bits and nonidentity192→1 final alias. These are original-context/helper witnesses, not complete retained zero-comparison/source-step Stock.lower witnesses.
- Combined51-module build passes450jobs. All100 public roots pass normal kernel/transitive and fresh compact-import MCP audits with only standard axioms. All51 original scans are clean. Prior47 comparison source hashes/88 trust sets and122 validated division source hashes remain unchanged. git diff --check passes. Receipt docs/research/stock-cmp-zero-checkpoint.json; complete archive /home/lee/.clifv-recovery/20261014T213114Z-zero/checkpoint.tar.gz. Local/unpublished HEAD remains01081291; comparison sources uncommitted.
- Next: actual zero-comparison652 selection/matching from original zero definitions/source typing; selected-root/output/retained binding/guarded original source transfer and complete driver witnesses. Continue32/narrow8/16/defined-operand/composite nonzero paths, predecessor/nonencodable/constant-LHS/both-constant/extended/fused comparisons, minmax/select and complete family gates preserving824 prior roots/exact seven compiler sets.
- Full original #140 remains active/incomplete; production legacy. All remaining uncovered families/effects/deferred sinking, source/block/whole-driver simulation and completeness, compiler/checker/linker/generated-proof integration and fresh complete Stock comparison remain mandatory. No push/merge; no full-family/full-repository gate claimed.


## Actual zero rule RHS and original constant matching

Updated UTC: 2026-10-14T21:41:57.661047+00:00

- Actual rule5172 inequality RHS derives its651 call; actual rule5170 equality RHS derives651 and649 calls with original full intermediate state/trace and sufficient fuel. RHS-plus715 source-value variants derive helper success internally and preserve original64-bit source predicates, final aliases, fresh result and other registers.
- Original defining zero data matches both actual RHS-zero rules with the exact canonical one-variable environment and unchanged complete match state/trace. First-match652 selection and higher mirrored-rule exclusion remain to be integrated.
- Combined54-module build passes453jobs. All105 roots pass normal and fresh compact-import MCP permitted-only transitive audits;54 original scans clean. Prior51 source hashes/100 trust sets and122 division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-zero-rhs-checkpoint.json. These five new roots still require explicit non-vacuity witnesses; no family-ready claim.
- Next: actual652 first-match selection, selected-root/output/retained/result binding, guarded original-source transfer and complete Stock.lower zero witnesses; then every recorded comparison alternative, minmax/select and full gates.
- Full original #140 remains active/incomplete. Uncovered families/effects/deferred sinking, source/block/whole-driver simulation and completeness, actual production integration across compiler/checker/linker/generated-proof consumers and fresh complete Stock comparison remain required. Production legacy; no push/merge.


## Integrated original RHS-zero comparison path

Updated UTC: 2026-10-14T21:53:44.218718+00:00

- Actual652 first-match selection now derives5170/5172 RHS, excluding higher mirrored rules from original parameter definition absence and later fallbacks from actual failed-prefix matches. Actual emitter/condition/output, selected source root, retained/result binding, guarded original-source transfer and getter-derived variants compile. Original DFG/restricted-frame/availability conditions retained.
- Complete actual ordinary-kernel Stock.lower runs and original retained/source-step witnesses cover64-bit eq(false) and ne(true), sparse IDs7/31/100, dirty upper input bits, unused zero constant with mapped register193 containing777, fresh result195 and guarded postavailability. The ne witness also inhabits the automatic getter-derived source-transfer variant.
- Combined62-module targeted build and117 normal/fresh MCP permitted-only transitive audits pass;62 original scans clean. Prior54 source hashes/105 trust sets and122 division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-zero-integrated-checkpoint.json. Earlier helper-only/witness-pending receipts remain historical.
- Next: opposite complete boolean outcomes and widths/boundaries; zero LHS/both constants/defined/composite-condition paths; predecessor/nonencodable/extended/fused comparisons, minmax/select and full comparison-family gates. Division remains last fully validated family.
- Full original #140 remains active/incomplete. Every uncovered family/effect/deferred-sinking, source/block/whole-driver simulation and completeness, production compiler/checker/linker/generated-proof integration and fresh complete Stock comparison obligation remains required. Production legacy; no push/merge.


## Original zero comparisons on either side, all64-bit operand values

Updated UTC: 2026-10-14T22:00:44.515134+00:00

- Complete original RHS-zero retained/source-step equality and inequality witnesses now quantify over arbitrary64-bit parameter operands. Both boolean outcomes and every64-bit boundary follow without additional input conditions; old fixed variants remain unchanged. Dirty128-bit upper input bits and unmaterialized zero constant register777 remain covered.
- Mirrored LHS-zero rules5171/5173 have actual match/first-match652 selection, actual emitter/condition/output, selected original source root, retained/result binding and guarded source-transfer/getter-derived proofs. Operand-order symmetry is proved in the source bool8 result; complete full Stock.lower witnesses quantify over arbitrary64-bit operands for both eq/ne, with sparse IDs7/31/100, real root958, fresh result195 and guarded postavailability.
- Combined73-module targeted build passes472jobs. All132 public roots pass normal kernel/transitive and fresh compact-import MCP permitted-only audits;73 original source scans clean. Prior62 source hashes/117 trust sets and122 validated division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-zero-left-all-values-checkpoint.json.
- Next:32/narrow8/16 zero paths, defined/composite nonzero alternatives and both constants; predecessor/nonencodable/extended/fused comparisons, minmax/select and full comparison-family gates preserving824 prior roots/exact seven compiler trust sets. Division remains last fully validated family.
- Full original #140 remains active/incomplete: every uncovered family/effect/deferred-sinking, source/block/whole-driver simulation and completeness, actual compiler/checker/linker/generated-proof production integration and fresh complete Stock comparison remains mandatory. Production legacy; no push/merge.


## Integrated original32-bit zero comparisons on either side

Updated UTC: 2026-10-14T22:14:18.639275+00:00

- Actual4977 RHS derives556 zero-extension execution and exact condition/full state/trace. Actual651 first-match selection on original32-bit parameters supplies this RHS internally, excluding higher second-result and incompatible-width patterns. Successful source requests/zero-extension derive the guarded mapping and complete marked state; actual715 and649 inversion preserve original32-bit predicates through final aliases.
- Both original operand orders now compose actual652/715/172 and selected958 source root, retained result binding/exact code/copy absence and guarded original-source transfer/getter-derived variants. Complete ordinary-kernel Stock.lower observations and retained/source-step witnesses quantify over arbitrary32-bit operands for eq/ne and zero on either side, including both boolean outcomes/all32-bit boundaries. Sparse IDs7/31/100, dirty128-bit upper input bits, unmaterialized constant register193=777, fresh result195, memory/other-register preservation and guarded postavailability remain covered.
- Combined93-module targeted build passes492jobs. All165 roots pass normal kernel/transitive and fresh compact-import MCP permitted-only audits;93 original source scans clean. Prior73 source hashes/132 trust sets and122 validated division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-zero32-integrated-checkpoint.json.
- Next:8-bit masked-test and16-bit zero/nonzero behavior/original accepted-input parity, defined/composite/both-constant zero paths; predecessor/nonencodable/extended/fused comparisons, minmax/select and full comparison-family gates preserving824 prior roots/exact seven compiler trust sets. Division remains last fully validated family.
- Full original #140 remains active/incomplete: every uncovered family/effect/deferred-sinking, source/block/whole-driver simulation and completeness, actual compiler/checker/linker/generated-proof production integration and fresh complete Stock comparison remains mandatory. Production legacy; no push/merge.


## Actual8-bit masked-test helper/source-value checkpoint

Updated UTC: 2026-10-14T22:31:29.813177+00:00

- Actual424 test builder preserves complete Stock state and records real size/test traces. Actual4988 RHS performs the guarded original request and derives its map, full marked state and exact TST255 producer from success. Actual651 first-match selection on original8-bit parameters derives4988 RHS internally, excluding higher second-result patterns and lower fallback rules. Actual RHS/715 and selected651/715 executions hold the original8-bit nonzero predicate through final aliases and preserve other registers.
- Kernel-checked TST255 low-byte truth and original8-bit predicate facts replace legacy native dependencies; equality uses the preserved standard-only inversion theorem. The initial failed native-dependency MCP audit is archived as historical diagnostic evidence. Actual649 explicit flag inversion preserves its producer/all Stock fields, with an inhabited witness for every condition variant. Actual RHS/649/715 equality-to-zero values and original accepted sparse-ID7 helper/source-value witnesses cover both boolean outcomes, dirty128-bit upper bits and nonidentity192-to1 alias. These remain helper/source-value witnesses, not complete retained8-bit Stock.lower comparison witnesses.
- The read-only16-bit eq/zero probe succeeds in both Stock and legacy lowering. Recorded Stock trace emits zero-extension16-to32, cmp0 and cseteq. Generated term111 is fits_in_32 (not exact-width ty_32); the16-bit path requires composition of the real temporary-write extension fragment. Probe evidence is observational and does not close general16-bit semantics/completeness/parity.
- Combined104-module targeted build passes503jobs. All181 public roots pass normal kernel/transitive and fresh compact-import MCP permitted-only audits;104 original scans clean. Prior93 source hashes/165 trust sets and122 validated division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-nonzero8-checkpoint.json.
- Next: actual8-bit zero652/root/retained/source integration and complete Stock.lower witnesses;16-bit extension/source/temp-frame composition and complete retained witnesses; defined/composite/both-constant, predecessor/nonencodable/extended/fused comparisons, minmax/select and full family gates. Full original #140 remains active/incomplete; every remaining family/effect/deferred-sinking/source-block-whole-driver simulation and completeness/actual production integration/fresh Stock comparison obligation remains required. Production legacy; no push/merge.


## Integrated original8-bit zero comparisons and16-bit helper composition

Updated UTC: 2026-10-14T22:43:28.173711+00:00

- Actual8-bit zero652 selection now derives its real helper/flag inversion calls internally; original selected958 source root and172 output establish source bool8 for both operand orders. Actual retained records derive fresh nonempty binding, exact TST255/cset code/copy absence, guarded original-source transfer and getter-derived variants under the original restricted DFG/availability/demand conditions.
- Complete ordinary-kernel Stock.lower observations and retained/original source-step witnesses cover arbitrary8-bit operands, eq/ne and zero on either side (all8-bit boundaries and both boolean outcomes). Sparse IDs7/31/100, dirty128-bit upper input bits, constant register193=777 deliberately unmaterialized, fresh result195, other-register/source-memory preservation and guarded postavailability remain covered.
- Actual16-bit4977 RHS/556 extension carries the original source value through its real temporary-write prefix and outside frame. Actual prefix-plus715 condition establishes original nonzero bool8 with preservation outside the entire fresh allocation interval. Checked accepted-original parameter helper witnesses quantify over arbitrary16-bit values, dirty upper bits and nonidentity192-to1 aliases; these remain helper/source-value witnesses, not complete retained16-bit comparison witnesses.
- Combined123-module targeted build passes522jobs. All209 roots pass normal kernel/transitive and fresh compact-import MCP standard-only audits;123 original source scans clean. Prior104 source hashes/181 trust sets and122 validated division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-zero8-integrated-checkpoint.json.
- Next:16-bit actual651/equality/zero652/root/retained/guarded original-source-step integration and complete driver witnesses; defined/composite/both-constant zero paths; predecessor/nonencodable/extended/fused comparisons, minmax/select and full comparison-family gates preserving824 prior roots/exact seven compiler trust sets. Division remains last fully validated family.
- Full original #140 remains active/incomplete: every uncovered family/effect/deferred-sinking, source/block/whole-driver simulation and completeness, actual compiler/checker/linker/generated-proof production integration and fresh complete Stock comparison remains mandatory. Production legacy; no push/merge.


## Integrated original16-bit zero comparisons and original-invariant selection

Updated UTC: 2026-10-14T22:57:25.843242+00:00

- Actual16-bit equality composes the real extension prefix,649 inversion and715 condition. The complete fresh-interval frame accounts for both temporary and boolean writes. Actual651 parameter selection, zero652/RHS/condition/output and selected original958 root establish source bool8 for both operand orders.
- Actual retained records derive fresh nonempty result binding and exact emitted prefix/cmp/cset code/copy absence. Guarded original-source and getter-derived transfer retain restricted DFG, availability, demand and memory. Complete ordinary-kernel Stock.lower observations and retained/original source-step witnesses cover arbitrary16-bit parameter operands, eq/ne and zero on either side (all boundaries and both outcomes). Sparse7/31/100, dirty128-bit upper input bits, unmaterialized constant register193=777, temporary195/fresh result196, correct outside-fresh-interval and guarded postavailability preservation remain covered.
- A new original-invariant16-bit helper selection theorem excludes all seven overflow alternatives using the existing mapped source invariant and removes the parameter-only premise. The old parameter variant remains unchanged. An actual original-context construction/execution witness inhabits the new statement; integration into defined/composite/both-constant retained paths remains next.
- Combined142-module targeted build passes541jobs. All237 public roots pass normal kernel/transitive and fresh compact-import MCP standard-only audits;142 original scans clean. Prior123 source hashes/209 trust sets and122 validated division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-zero16-integrated-checkpoint.json.
- Next: original-invariant helper selection for defined/composite/both-constant operands at all widths; predecessor/nonencodable/extended/fused comparisons, minmax/select and complete comparison-family gates preserving824 prior roots/exact seven compiler trust sets. Division remains last fully validated family.
- Full original #140 remains active/incomplete: every uncovered family/effect/deferred-sinking, source/block/whole-driver simulation and completeness, actual compiler/checker/linker/generated-proof production integration and fresh complete Stock comparison remains mandatory. Production legacy; no push/merge.


## Original-invariant16-bit defined/both-constant zero comparisons

Updated UTC: 2026-10-14T23:13:47.498604+00:00

- New original-invariant16-bit RHS/source, constant-left652 emission, selected958/172 output, retained binding and guarded original-source/getter-derived variants remove parameter-only premises. Old parameter variants and all original DFG/availability/demand conditions remain unchanged.
- Complete ordinary-kernel Stock.lower observations and original retained/source-step eq/ne witnesses cover a real preceding negation over arbitrary16-bit parameter values, actual defined source31 and final alias193-to198. Original sparse7/31/63/100, dirty128-bit upper bits, looked-through zero register194=777 deliberately unmaterialized, temporary196/result197, outside-fresh-interval/source-memory/postavailability preservation remain covered.
- Complete ordinary-kernel both-constant driver observations and original retained/source-step witnesses cover eq/ne for zero-vs-zero and zero-vs-three, with real demanded-constant alias193-to198 and unmaterialized looked-through zero. These exercise the original-invariant retained variants without adding caller selection/helper/binding certificates.
- Original-invariant nonzero helper selection is now proved at8/16/32/64 widths using existing mapped-source overflow exclusions, with original-context actual execution witnesses and unchanged old variants. Integration into analogous8/32/64 defined/both-constant retained paths remains next.
- Combined161-module targeted build passes560jobs. All261 roots pass normal kernel/transitive and fresh compact-import MCP standard-only audits;161 original scans clean. Prior142 source hashes/237 trust sets and122 validated division hashes unchanged; git diff --check passes. Receipt docs/research/stock-cmp-defined16-checkpoint.json.
- Next: original-invariant8/32/64 source/root/retained and complete defined/both-constant witnesses; RHS-zero nonconstant first-match variants; predecessor/nonencodable/extended/fused comparisons, minmax/select and complete family gates preserving824 prior roots/exact seven compiler trust sets. Division remains last fully validated family.
- Full original #140 remains active/incomplete: every uncovered family/effect/deferred-sinking, source/block/whole-driver simulation and completeness, actual compiler/checker/linker/generated-proof production integration and fresh complete Stock comparison remains mandatory. Production legacy; no push/merge.


## Original-invariant32-bit defined/both-constant comparisons

Updated UTC: 2026-10-14T23:24:23.410666+00:00

- New original-invariant32-bit helper/RHS/source, constant-left652 emission, selected958/172 output, retained binding and guarded source/getter-derived variants remove parameter-only premises. Old variants and original DFG/availability/demand conditions preserved.
- Complete ordinary-kernel Stock.lower/source-step eq/ne witnesses cover preceding negation over arbitrary32-bit inputs and both constants zero-vs-zero/zero-vs-three. Sparse7/31/63/100, actual alias193-to197, dirty128-bit upper bits, unmaterialized zero register194=777, result196 and other-register/memory/postavailability preservation checked.
- Combined175-module targeted build: 574 jobs;281 normal/fresh MCP standard-only roots;175 original scans clean. Prior161 source hashes/261 trust sets and122 division hashes unchanged. Receipt docs/research/stock-cmp-defined32-checkpoint.json.
- Next: analogous8/64 original-invariant integration and complete defined/both-constant witnesses; RHS-zero nonconstant selection; remaining comparison forms/minmax/select and full family gates. Full original #140 obligations remain active/incomplete, production legacy, no push/merge.


## Original-invariant8/64-bit defined/both-constant comparisons

Updated UTC: 2026-10-14T23:33:41.801114+00:00

- New original-invariant8/64-bit helper/RHS/source, constant-left652 emission, selected958/172 output, retained binding and guarded source/getter-derived variants remove parameter-only premises. Old variants and original DFG/availability/demand conditions preserved.
- Complete ordinary-kernel Stock.lower/source-step eq/ne witnesses cover preceding negation over arbitrary8/64-bit inputs and both constants zero-vs-zero/zero-vs-three. Sparse7/31/63/100, actual alias193-to197, dirty128-bit upper bits, unmaterialized zero register194=777, result196 and other-register/memory/postavailability preservation checked.
- Combined202-module targeted build: 601 jobs;319 normal standard-only roots,38 fresh MCP audits and281 reused unchanged prior MCP audits;202 original scans clean. Prior175 source hashes/281 trust sets and122 division hashes unchanged. Receipt docs/research/stock-cmp-defined8-64-checkpoint.json.
- Next: RHS-zero nonconstant selection; remaining comparison forms/minmax/select and full family gates. Full original #140 obligations remain active/incomplete, production legacy, no push/merge.


## Original-invariant zero-right defined-source comparisons

Updated UTC: 2026-10-14T23:41:16.224182+00:00

- Actual652 zero-right first-match selection uses original mapped-source nonconstant classification to exclude higher mirrored constant rules. This is a source-classification branch; full-family dispatch must derive classification internally. No caller match/helper/binding certificates introduced, old parameter variants retained.
- Original-invariant8/16/32/64 emitter/root958/output172, retained binding and guarded original-source/getter-derived transfer compile. Complete actual ordinary-kernel Stock.lower/source-step eq/ne witnesses cover preceding negation over arbitrary inputs at every width, sparse7/31/63/100, dirty128-bit upper bits and unmaterialized zero register194=777.
- Actual alias193-to197/result196 at8/32/64; alias193-to198/temporary196/result197 and correct outside-allocation-interval frame at16. Source-memory and postavailability preserved.
- Combined231-module build: 630 jobs;364 normal standard-only roots,45 fresh MCP audits and319 reused prior results after checking all202 prior source hashes and319 trust sets unchanged;231 original scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-zero-right-defined-checkpoint.json.
- Next: remaining comparison forms/all-condition/all-width coverage, minmax/select and complete family gates. Every original whole-driver/effect/deferred-sinking/completeness/production-integration obligation remains required; production legacy, full #140 active/incomplete, no push/merge.


## Publication discipline changed; first three batches landed

Updated UTC: 2026-10-14T23:55:33.744899+00:00

The user now authorizes pushes for remote backup and roughly three validated squash-merged PRs per day, superseding the earlier prohibition. #180 fused-NOT, #181 multiplication/fused multiplication and #182 scalar shifts/helper foundations are merged with all three CI checks successful for each. Main 70d187b2fbdb55a1954a9cbcb566b68feab1798b exactly matches the previously validated30f48dc tree. All three measurements preserve671 exact matches with0 gains/0 losses; this proof-only publication does not complete the production cutover.

Validated stack and all comparison WIP were pushed to dedicated remote backup branches, preserving the active worktree branch/index. See docs/plans/stock-driver-publication.md and docs/research/stock-driver-publication-20261014.json. Continue remaining comparison forms/full family gates and every original #140 whole-driver/effect/simulation/completeness/production-integration obligation. Goal active/incomplete; production legacy.


## Adjusted-immediate predecessor source-value checkpoint

Updated UTC: 2026-10-15T00:05:12.560531+00:00

- Actual unsigned5155/signed5160 adjusted RHS executions derive guarded source requests, exact flag producers and full marked state. Real715 condition execution preserves original unsigned/signed greater-or-equal predicates at32/64 bits.
- Original restricted DFG/getters tie the predecessor immediate to the actual source constant. The rule odd-literal guard excludes zero/signed minimum internally. Accepted original-context RHS/715 witnesses cover arbitrary64-bit inputs, shifted/unshifted encodings, sparse7/31, dirty128-bit upper bits, nonidentity192-to1 alias and unmaterialized constant register193=777.
- Combined241-module targeted build: 640 jobs;380 normal standard-only roots,16 new MCP checks and364 prior results reused after confirming all231 source hashes/364 trust sets unchanged;241 original scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-predecessor-checkpoint.json.
- Next canonical5155/5160 match/selected652, original958/172 and retained/result-binding/guarded source-step integration, then complete actual Stock.lower witnesses. Current witness scope is original-context RHS/715, not complete predecessor retained/source-step coverage. Other comparison forms/minmax/select and full family gates remain.
- All original #140 whole-driver/effect/completeness/production obligations remain mandatory; goal active/incomplete, production legacy. Publication now authorized; three prior validated families landed #180/#181/#182 on October14, and WIP backups are pushed after checkpoints.


## Actual predecessor matching and first-match selection

Updated UTC: 2026-10-15T00:17:35.434426+00:00

- Canonical5155/5160 matching derives the exact normalized four-field environment, wrapping subtraction and unchanged state/trace at32/64 machine widths. No caller normalization premise added.
- Real652 selection excludes the higher ordinary immediate5165 using nonencodability of the original constant, incompatible zero/opposite-condition rules, and later fallbacks using actual earlier successful matching.
- Ordinary-kernel selected-helper witnesses use accepted original i64 comparison contexts with4097/8193 and shifted predecessors4096/8192. Earlier unshifted RHS witnesses remain helper witnesses; encodable original constants select the ordinary immediate path.
- Combined247 modules/646 jobs;386 normal standard-only roots,6 fresh MCP checks and380 reused after confirming all241 prior source hashes/trust sets unchanged;247 original scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-predecessor-selection-checkpoint.json.
- Next transport the unused normalized literal slot2 into the existing source-value contract; compose selected652/715 and original958/172, then retained/result binding, guarded source-step transfer and complete Stock.lower witnesses. Other forms/minmax/select/full family gates and every original whole-driver/effect/completeness/production obligation remain required. Goal active/incomplete; production legacy; remote backups/publication cadence authorized.


## Integrated predecessor retained/source execution

Updated UTC: 2026-10-15T00:31:20.393472+00:00

- Actual652/715 source semantics, original958/172 selected-root output, retained-result binding and exact compare/cset/copy absence compose for unsigned/signed predecessor comparisons at32/64 bits. Unused normalized literal slot is transported through internally derived RHS replay; old variants preserved.
- Guarded original-source/getter-derived transfer preserves original restricted DFG, demand, availability and memory. Eight complete ordinary-kernel Stock.lower/retained/source-step witnesses cover signed/unsigned32/64 with4097/8193 originals and4096/8192 shifted predecessors over arbitrary input words. Sparse7/31/100, dirty128-bit upper bits, constant193=777 deliberately unmaterialized, fresh boolean195, all other registers and postavailability preservation checked.
- Combined267 modules/666 jobs;412 normal standard-only roots,26 fresh MCP checks and386 prior results reused after confirming all247 prior sources/axiom sets unchanged;267 original scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-predecessor-integrated-checkpoint.json.
- Next remaining nonencodable/extended/fused comparison alternatives/all-condition/all-width dispatch, minmax/select and complete family/full-repository gates preserving824 prior roots/exact seven compiler sets. Every original whole-driver/effect/completeness/production obligation remains required. Goal active/incomplete; production legacy; remote backups/publication cadence authorized.


## Nonencodable constant register fallback

Updated UTC: 2026-10-15T00:59:03.537921+00:00

- Ordinary/predecessor immediate and zero-rule matching failures preserve full state/trace under original source-literal exclusions, for all integer conditions. Actual5128 fallback selection,652/715 values and958/172 output are internally derived. An explicit-case proof replaces expensive matcher backtracking and passes a500000-heartbeat bound.
- Retained binding/exact compare-cset/copy absence and guarded original-source/getter-derived transfer preserve original DFG, demand, availability and memory. Four complete ordinary-kernel Stock.lower/retained/source-step witnesses cover signed/unsigned32/64 over arbitrary inputs against70003.
- Actual two-instruction constant materialization installs alias193-to197; source-held constant is read from197, raw193=777 deliberately stale. Dirty128-bit upper bits, fresh boolean195, all other registers and postavailability preservation checked. This is a real nonidentity alias crossing the comparison allocation interval.
- Combined279 modules/678 jobs;429 normal standard-only roots,17 fresh MCP checks and412 prior results reused after confirming all267 prior source hashes/trust sets unchanged;279 original scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-nonencodable-checkpoint.json.
- Next extended/fused/narrow alternatives, constant-left classifications and all-condition/all-width dispatch, minmax/select and full family/repository gates. Every original whole-driver/effect/completeness/production obligation remains required. Goal active/incomplete, production legacy, publication/backups authorized.


## Narrow comparison RHS and machine core

Updated UTC: 2026-10-15T01:13:29.981409+00:00

- Actual555/556 source requests allocate the32-bit extension temporary and preserve complete scheduling state. Actual657 supplies all four right-extension encodings. Actual5117/5108 RHS composes left extension/right request/exact producer/full state.
- Standard-kernel narrow flag proof covers arbitrary8/16-bit operands and every condition, deriving Arm register-extension semantics without native lemmas. Actual extended compare/cset execution through final aliases preserves all outside-result registers. Sparse RHS/request witnesses and nonidentity-alias boundary witnesses pass.
-285 modules/684 jobs;439 normal standard-only roots,10 fresh MCP checks,429 prior results reused after confirming all279 prior source hashes/trust sets unchanged;285 original-source scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-narrow-core-checkpoint.json.
- Next derive guards from successful RHS and compose actual left-extension execution/715; narrow first-match selection5117/5108/5134,958/172 outputs, retained binding/guarded source/getter transfer and complete actual Stock.lower/source-step witnesses. Helper/RHS/machine-pair witnesses do not discharge complete-driver nonvacuity. Other forms/minmax/select/full family/repository gates and every original effect/whole-driver/completeness/production obligation remain. Goal active/incomplete, production legacy.


## Narrow comparison source-value composition

Updated UTC: 2026-10-15T01:23:21.032212+00:00

- Actual5117/5108 success derives original guards/mappings through real555/556 inversion; typing and RHS replay derive exact producer/full state.
- Real left extension and real715 compare/cset compose to original8/16 predicate under final aliases, preserving the outside allocation interval. The internal right-source separation obligation remains explicit and must be derived from original retained-record availability.
- Constructed real source contexts inhabit the actual RHS/715/value pipeline for arbitrary word pairs, both widths/signednesses, sparse7/31/100 and dirty128-bit upper bits. These are source-pipeline witnesses, not complete retained Stock.lower/source-step witnesses.
-288 modules/687 jobs;443 normal standard-only roots,4 fresh MCP checks and439 reused after verifying285 prior hashes/trust sets unchanged;288 original-source scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-narrow-values-checkpoint.json.
- Next narrow first-match5117/5108/5134 and652/715/original958/172, derive right-source scratch separation from original availability, retained result binding/guarded source/getter transfer and complete Stock.lower/source-step witnesses; other forms/minmax/select/all family/repository/full-goal effects/simulation/completeness/production obligations retained. Goal active/incomplete, production legacy.


## Narrow nonconstant comparison retained/source integration

Updated UTC: 2026-10-15T01:33:43.952021+00:00

- Actual5117/5108 first-match selection derives canonical environment/trace under original nonconstant classifications at8/16, for every integer condition. Actual652/715 and original958/172 selected outputs compute original predicates.
- Structural selected allocation proves exactly two registers independently of machine values. Actual retained-record availability plus this allocation discharges right-source scratch separation internally; result binding/copy absence, exact extension/extended-compare/cset execution and guarded original-source/getter transfer pass with original restricted DFG, demand/availability and memory preserved.
- Four complete ordinary-kernel actual Stock.lower/retained/source-step witnesses cover arbitrary pairs at8/16 signed/unsigned, sparse7/31/100, real958 root, dirty128-bit upper bits, parameter aliases and complete outside-allocation/postavailability preservation. Earlier helper-only limitation is discharged for these nonconstant forms.
-300 modules/699 jobs;456 normal standard-only roots,13 fresh MCP checks and443 reused after verifying288 prior hashes/trust sets unchanged;300 original-source scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-narrow-integrated-checkpoint.json.
- Next narrow constant5134 and remaining constant/constant-left classifications, all-condition/all-width dispatch, minmax/select and complete family/repository gates. Every original effects/whole-driver simulation/completeness/production obligation remains; goal active/incomplete, production legacy.


## Narrow constant immediate retained/source integration

Updated UTC: 2026-10-15T01:47:42.036839+00:00

- Actual5134 RHS derives guarded original left request/zero-extension, exact immediate producer and full state. Original defining-constant metadata/restricted DFG ties encoded bits to unsigned8/16 source semantics without materializing the constant.
- Actual5134 first-match selection derives canonical environment/trace for all unsigned/equality conditions under original nonconstant-left/nonzero-encodable-right and narrow typing. Wide-rule rejection uses direct failure proofs instead of expensive inversion. Actual652/715/original958/172, retained binding/copy absence and guarded original-source/getter transfer pass.
- Four complete ordinary-kernel actual Stock.lower/retained/source-step witnesses cover arbitrary input words against3/129 at8 bits and3/4096 at16 bits. Raw constant slot193=777 is deliberately unrelated and demand31=0; real scratch/boolean allocation, dirty128-bit upper bits and full outside-allocation/postavailability preservation checked.
-314 modules/713 jobs;472 normal standard-only roots,16 fresh MCP checks and456 reused after verifying300 prior hashes/trust sets unchanged;314 original-source scans clean and122 division hashes unchanged. Receipt docs/research/stock-cmp-narrow-immediate-checkpoint.json.
- Next narrow constant register fallbacks, constant-left classifications/all-condition/all-width dispatch, minmax/select and complete comparison-family/repository gates. All original effects/whole-driver simulation/completeness/production obligations retained; goal active/incomplete, production legacy.
